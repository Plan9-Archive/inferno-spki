/*
 * Inferno public-key authentication, protocol version 1
 *	based on GSoC 2007 project (Katie Reynolds)
 */
#include "std.h"
#include "dat.h"

#define MAXMSG 4096

typedef struct InfPublicKey InfPublicKey;
typedef struct InfPrivateKey InfPrivateKey;
typedef struct Certificate Certificate;
typedef struct Authinfo Authinfo;

struct InfPublicKey {
	RSApub*	pk;
	char*	owner;
};

struct InfPrivateKey {
	RSApriv*	sk;
	char*	owner;
};

struct Certificate {
	char*	sa;
	char*	ha;
	char*	signer;
	int	exp;
	mpint*	sig;
};

struct Authinfo {
	InfPrivateKey*	mysk;
	InfPublicKey*	mypk;
	Certificate*	cert;
	InfPublicKey*	spk;
	mpint*	alpha;
	mpint*	p;
};

static Certificate*	sign(InfPrivateKey*, int, uchar*, int);
static int	verify(InfPublicKey*, Certificate*, char*, int);
static int	infrsaverify(mpint*, mpint*, RSApub*);
static char*	pktostr(InfPublicKey*);
static void	pkfree(InfPublicKey*);
static char*	certtostr(Certificate*);
static void	certfree(Certificate*);
static Certificate*	mkcert(char*, char*, char*, int, mpint*);
static Certificate*	strtocert(char*);
static InfPublicKey*	strtopk(char*);
static InfPrivateKey*	strtosk(char*);
static void	skfree(InfPrivateKey*);
static Authinfo*	keytoauthinfo(Key*);
static void	infofree(Authinfo*);
static int	mptob64z(mpint*, char*, int);

static int	readmsg(Conv*, char**);
static int	sendstrfree(Conv*, char*);
static int	sendstr(Conv*, char*);
static void	senderr(Conv *, char*, ...);
#pragma varargck	argpos senderr 2

static int
infauthclient(Conv *c)
{
	Key *k;
	Attr *attr;
	Authinfo *info;
	Certificate *hiscert, *alphacert;
	InfPublicKey *hispk;
	mpint *p, *r0, *alphar0, *alphar1, *alphar0r1;
	char *buf, *alphabuf;
	uchar *cvb;
	int ret, n;
	long now;

	k = nil;
	alphar0 = alphar1 = alphar0r1 = r0 = p = nil;
	hiscert = nil;
	alphacert = nil;
	hispk = nil;
	info = nil;
	alphabuf = emalloc(MAXMSG);
	buf = nil;

	c->state = "find key";
	attr = delattr(copyattr(c->attr), "role");
	k = keyfetch(c, "%A %s", attr, c->proto->keyprompt);
	freeattr(attr);
	if(k == nil)
		return -1;
	c->attr = addattrs(c->attr, k->attr);

	ret = -1;

	info = k->priv;
	c->state = "write version";
	if(sendstr(c, "1") < 0)
		goto Stop;

	c->state = "read version";
	if(readmsg(c, &buf) < 0)
		goto Stop;

	if(atoi(buf) != 1){
		senderr(c, "incompatible authentication protocol");
		goto Stop;
	}

	r0 = mpnew(0);
	alphar0 = mpnew(0);
	alphar0r1 = mpnew(0);

	c->state = "write alphar0";
	p = info->p;
	mprand(mpsignif(p), genrandom, r0);
	mpexp(info->alpha, r0, p, alphar0);
	mptob64z(alphar0, alphabuf, MAXMSG);
	if(sendstr(c, alphabuf) < 0)
		goto Stop;

	c->state = "write cert";
	if(sendstrfree(c, certtostr(info->cert)) < 0)
		goto Stop;

	c->state = "write pk";
	if(sendstrfree(c, pktostr(info->mypk)) < 0)
		goto Stop;

	c->state = "read alphar1";
	if(readmsg(c, &buf) < 0)
		goto Stop;

	alphar1 = strtomp(buf, nil, 64, nil);
	/* check below that alphar1 is in range, after cert check */
	if(mpcmp(alphar0, alphar1) == 0){
		senderr(c, "possible replay attack");
		goto Stop;
	}

	c->state = "read cert";
	if(readmsg(c, &buf) < 0)
		goto Stop;

	hiscert = strtocert(buf);
	if(hiscert == nil){
		senderr(c, "bad certificate syntax");
		goto Stop;
	}

	c->state = "read pk";
	if(readmsg(c, &buf) < 0)
		goto Stop;

	hispk = strtopk(buf);
	if(hispk == nil){
		senderr(c, "bad public key syntax");
		goto Stop;
	}

	if(verify(info->spk, hiscert, buf, strlen(buf)) == 0){
		senderr(c, "pk doesn't match certificate");
		goto Stop;
	}

	now = time(nil);
	if(hiscert->exp != 0 && hiscert->exp <= now){
		senderr(c, "certificate expired");
		goto Stop;
	}

	c->state = "write alpha cert";
	n = mptob64z(alphar0, alphabuf, MAXMSG);
	n += mptob64z(alphar1, alphabuf + n, MAXMSG - n);
	alphacert = sign(info->mysk, 0, (uchar*)alphabuf, n);
	memset(alphabuf, 0, n);

	if(sendstrfree(c, certtostr(alphacert)) < 0)
		goto Stop;

	c->state = "read alpha cert";
	if(readmsg(c, &buf) < 0)
		goto Stop;
	certfree(alphacert);
	alphacert = strtocert(buf);
	if(alphacert == nil){
		senderr(c, "bad certificate syntax");
		goto Stop;
	}

	n = mptob64z(alphar1, alphabuf, MAXMSG);
	n += mptob64z(alphar0, alphabuf + n, MAXMSG - n);
	if(!verify(hispk, alphacert, alphabuf, n)){
		senderr(c, "signature did not match pk");
		goto Stop;
	}

	if(mpcmp(info->p, alphar1) <= 0){
		senderr(c, "implausible parameter value");
		goto Stop;
	}

	mpexp(alphar1, r0, info->p, alphar0r1);
	n = mptobe(alphar0r1, nil, MAXMSG, &cvb);
	if(n < 0){
		senderr(c, "internal: can't convert secret");
		goto Stop;
	}
	c->attr = addattr(c->attr, "secret=%.*H", n, cvb);
	if(debug)
		fprint(2, "secret=%.*H\n", n, cvb);
	free(cvb);
	c->attr = addattr(c->attr, "cuid=%q", info->mypk->owner);	/* TO DO: which names to use? */
	c->attr = addattr(c->attr, "suid=%q", hispk->owner);
	c->attr = addattr(c->attr, "cap=''");	/* TO DO */
	if(debug)
		fprint(2, "attrs: %A\n", c->attr);

	c->state = "write response";
	sendstr(c, "OK");

	c->state = "read response";
	while(readmsg(c, &buf) >= 0){
		if(strcmp(buf, "OK") == 0){
			ret = 0;
			break;
		}
	}

Stop:
	free(buf);
	mpfree(r0);
	mpfree(alphar0);
	mpfree(alphar1);
	mpfree(alphar0r1);
	certfree(hiscert);
	certfree(alphacert);
	pkfree(hispk);
	free(alphabuf);

	keyclose(k);

	return ret;
}

static int
infauthcheck(Key *k)
{
	fmtinstall('B', mpfmt);
	if((k->priv = keytoauthinfo(k)) == nil){
		werrstr("malformed key data");
		return -1;
	}
	return 0;
}

static void
infofree(Authinfo *info)
{
	if(info == nil)
		return;
	skfree(info->mysk);
	pkfree(info->mypk);
	certfree(info->cert);
	pkfree(info->spk);
	mpfree(info->alpha);
	mpfree(info->p);
	free(info);
}

static void
infauthclosekey(Key *k)
{
	Authinfo *info;

	info = k->priv;
	infofree(info);
}

static void
senderr(Conv *c, char *f, ...)
{
	va_list ap;
	char err[ERRMAX], *buf;

	va_start(ap, f);
	vsnprint(err, sizeof(err), f, ap);
	va_end(ap);
	convprint(c, "!%.3d\n%s", strlen(err), err);
	buf = nil;
	while(readmsg(c, &buf) >= 0){
		/* flush until OK or an error; we don't care which */
		if(strcmp(buf, "OK") == 0)
			break;
	}
	free(buf);
	errstr(err, sizeof(err));
}

static int
sendstrfree(Conv *c, char *s)
{
	int r;

	r = sendstr(c, s);
	free(s);
	return r;
}

static int
sendstr(Conv *c, char *s)
{
	/* we can assume for now that it's printable */
	return convprint(c, "%.4d\n%s", strlen(s), (char*)s);
}

static int
readmsg(Conv *c, char **x)
{
	char hdr[6], *p;
	int i;

	free(*x);
	*x = nil;
	hdr[5] = 0;
	if(convread(c, hdr, 5) < 0)
		return -1;
	if(hdr[0] == '!')
		i = strtoul(hdr+1, nil, 10);
	else
		i = strtoul(hdr, nil, 10);
	if(i < 0 || i > MAXMSG){
		senderr(c, "bad auth message count");
		return -1;
	}
	*x = emalloc(i+1);
	if(convread(c, *x, i) < 0)
		return -1;
	(*x)[i] = 0;
	if(hdr[0] == '!'){
		/* acknowledge the error */
		p = "failed";
		convprint(c, "!%.3d\n%s", strlen(p), p);
		if(strncmp(*x, "remote: ", 8) == 0)	/* old implementation sent it */
			werrstr("%s", *x+8);
		else
			werrstr("remote: %s", *x);
		free(*x);
		*x = nil;
		return -1;
	}
	return 0;
}

static Certificate *
sign(InfPrivateKey *sk, int exp, uchar *a, int len)
{
	Certificate *cert;
	DigestState *ds;
	uchar digest[SHA1dlen];
	char	*buf;
	mpint *b, *sig;
	int n;

	buf = emalloc(MAXMSG);
	if(buf == nil)
		return nil;

	n = snprint(buf, MAXMSG, "%s %ud", sk->owner, exp);

	ds = sha1(a, len, 0, nil);
	sha1((uchar*)buf, n, digest, ds);
	free(buf);

	b = betomp(digest, SHA1dlen, nil);
	if(b == nil)
		return nil;
	sig = rsadecrypt(sk->sk, b, nil);
	cert = mkcert("rsa", "sha1", sk->owner, exp, sig);
	mpfree(b);
	mpfree(sig);

	return cert;
}

static int
verify(InfPublicKey *pk, Certificate *cert, char *a, int len)
{
	DigestState *ds;
	uchar digest[SHA1dlen];
	char	*buf;
	mpint *b;
	int n;

	if(strcmp(cert->sa, "rsa") != 0 ||
	   strcmp(cert->ha, "sha1") != 0 && strcmp(cert->ha, "sha") != 0)
		return 0;
	buf = emalloc(MAXMSG);
	if(buf == nil)
		return 0;
	n = snprint(buf, MAXMSG, "%s %d", cert->signer, cert->exp);
	ds = sha1((uchar*)a, len, 0, nil);
	sha1((uchar*)buf, n, digest, ds);
	free(buf);
	b = betomp(digest, SHA1dlen, nil);
	if(b == nil)
		return 0;
	n = infrsaverify(b, cert->sig, pk->pk);
	mpfree(b);
	return n;
}

static int
infrsaverify(mpint *m, mpint *sig, RSApub *key)
{
	mpint *t;
	int v;

	t = rsaencrypt(key, sig, nil);
	v = mpcmp(t, m) == 0;
	mpfree(t);
	return v;
}

static Certificate*
mkcert(char *sa, char *ha, char *signer, int exp, mpint *sig)
{
	Certificate *cert;

	cert = emalloc(sizeof(Certificate));
	cert->sa = estrdup(sa);
	cert->ha = estrdup(ha);
	cert->signer = estrdup(signer);
	cert->exp = exp;
	cert->sig = mpcopy(sig);
	return cert;
}

static char*
certtostr(Certificate *cert)
{
	char	*sigstr, *certstr;

	sigstr = emalloc(MAXMSG);
	mptob64z(cert->sig, sigstr, MAXMSG);
	certstr = smprint("%s\n%s\n%s\n%d\n%s\n", cert->sa, cert->ha, cert->signer, cert->exp, sigstr);
	free(sigstr);
	return certstr;
}

static Certificate*
strtocert(char *s)
{
	Certificate *cert;
	char	*a[5];

	if(s == nil)
		return nil;
	s = estrdup(s);
	if(getfields(s, a, 5, 0, "\n^") < 5 || strcmp(a[0], "rsa") != 0){
		free(s);
		return nil;
	}
	cert = emalloc(sizeof(Certificate));
	cert->sa = estrdup(a[0]);
	cert->ha = estrdup(a[1]);
	cert->signer = estrdup(a[2]);
	cert->exp = atoi(a[3]);
	cert->sig = strtomp(a[4], nil, 64, nil);
	free(s);
	return cert;
}

static void
certfree(Certificate *cert)
{
	if(cert == nil)
		return;
	free(cert->sa);
	free(cert->ha);
	free(cert->signer);
	mpfree(cert->sig);
	free(cert);
}

static InfPublicKey*
strtopk(char *s)
{
	InfPublicKey *pk;
	char	*a[4];

	if(s == nil)
		return nil;
	s = estrdup(s);
	if(getfields(s, a, 4, 0, "\n^") < 4 || strcmp(a[0], "rsa") != 0){
		free(s);
		return nil;
	}
	pk = emalloc(sizeof(InfPublicKey));
	pk->owner = estrdup(a[1]);
	pk->pk = rsapuballoc();
	pk->pk->n = strtomp(a[2], nil, 64, nil);
	pk->pk->ek = strtomp(a[3], nil, 64, nil);
	free(s);
	return pk;
}

static char*
pktostr(InfPublicKey *pk)
{
	char	*nstr, *ekstr, *pkstr;

	nstr = emalloc(MAXMSG);
	ekstr = emalloc(MAXMSG);

	mptob64z(pk->pk->n, nstr, MAXMSG);
	mptob64z(pk->pk->ek, ekstr, MAXMSG);

	pkstr = smprint("rsa\n%s\n%s\n%s\n", pk->owner, nstr, ekstr);

	free(ekstr);
	free(nstr);

	return pkstr;
}

static void
pkfree(InfPublicKey *pk)
{
	if(pk == nil)
		return;
	rsapubfree(pk->pk);
	free(pk);
}

static InfPrivateKey*
strtosk(char *s)
{
	InfPrivateKey *sk;
	mpint *n, *e, *d, *p, *q;
	char	*a[7];

	if(s == nil)
		return nil;
	s = estrdup(s);
	if(getfields(s, a, 7, 0, "\n^") < 7 || strcmp(a[0], "rsa") != 0){
		free(s);
		return nil;
	}

	sk = emalloc(sizeof(InfPrivateKey));
	sk->owner = estrdup(a[1]);
	n = strtomp(a[2], nil, 64, nil);
	e = strtomp(a[3], nil, 64, nil);
	d = strtomp(a[4], nil, 64, nil);
	p = strtomp(a[5], nil, 64, nil);
	q = strtomp(a[6], nil, 64, nil);
	sk->sk = rsafill(n, e, d, p, q);
	mpfree(n);
	mpfree(e);
	mpfree(d);
	mpfree(p);
	mpfree(q);
	free(s);
	return sk;
}

static void
skfree(InfPrivateKey *sk)
{
	if(sk == nil)
		return;
	free(sk->owner);
	rsaprivfree(sk->sk);
	free(sk);
}

static Authinfo*
keytoauthinfo(Key *k)
{
	Authinfo *info;
	char	*a;

	info = emalloc(sizeof(Authinfo));

	if((a = _strfindattr(k->privattr, "!sk")) == nil || (info->mysk = strtosk(a)) == nil)
		goto Error;
	if((a = _strfindattr(k->attr, "pk")) == nil || (info->mypk = strtopk(a)) == nil)
		goto Error;
	if((a = _strfindattr(k->attr, "cert")) == nil || (info->cert = strtocert(a)) == nil)
		goto Error;
	if((a = _strfindattr(k->attr, "spk")) == nil || (info->spk = strtopk(a)) == nil)
		goto Error;
	if((a = _strfindattr(k->attr, "dh-alpha")) == nil || (info->alpha = strtomp(a, nil, 16, nil)) == nil)
		goto Error;
	if((a = _strfindattr(k->attr, "dh-p")) == nil || (info->p = strtomp(a, nil, 16, nil)) == nil)
		goto Error;

	return info;

Error:
	infofree(info);
	return nil;
}

static int
mptob64z(mpint *b, char *buf, int len)
{
	uchar *p;
	int n, rv, o;

	n = (b->top + 1) * Dbytes;
	p = emalloc(n + 1);
	if(p == nil)
		goto err;

	n = mptobe(b, p + 1, n, nil);
	if(n < 0)
		goto err;

	p[0] = 0;
	if(n != 0 && (p[1] & 0x80)){
		/* force leading 0 byte for compatibility with older representation */
		o = 0;
		n++;
	} else
		o = 1;

	rv = enc64(buf, len, p + o, n);
	free(p);

	return rv;

err:
	free(p);
	if(len > 0){
		*buf = '*';
		return 1;
	}
	return 0;
}

static Role infauthroles[] =
{
	"client",	infauthclient,
	"server",	infauthclient,
	0
};

Proto infauth = {
	"infauth",
	infauthroles,
	// TODO: Should this be the keyprompt?
	"user?",
	infauthcheck,
	infauthclosekey,
};
