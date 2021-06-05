/*
 * Inferno public-key authentication, protocol version 1
 *	based on GSoC 2007 project (Katie Reynolds)
 */

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

struct State {
	int	version;
	Authinfo*	info;
	mpint*	alphar0;
	mpint*	alphar1;
	mpint*	alphar0r1;
	mpint*	r0;
	Certificate*	hiscert;
	InfPublicKey*	hispk;
	Key*	key;
	int	failed;
	char	rerr[ERRMAX];
	char	buf[MAXMSG];
};

enum
{
	CHaveVersion,
	CNeedVersion,
	CHaveAlphar0,
	CHaveCert,
	CHavePk,
	CNeedAlphar1,
	CNeedCert,
	CNeedPk,
	CHaveAlphaCert,
	CNeedAlphaCert,
	CHaveOk,
	CNeedOk,
	CHaveErr,
	CReadErr,

	Maxphase
};

static char*	phasenames[Maxphase] = 
{
	[CHaveVersion] "CHaveVersion",
	[CNeedVersion] "CNeedVersion",
	[CHaveAlphar0] "CHaveAlphar0",
	[CHaveCert] "CHaveCert",
	[CHavePk] "CHavePk",
	[CNeedAlphar1] "CNeedAlphar1",
	[CNeedCert] "CNeedCert",
	[CNeedPk] "CNeedPk",
	[CHaveAlphaCert] "CHaveAlphaCert",
	[CNeedAlphaCert] "CNeedAlphaCert",
	[CHaveOk] "CHaveOk",
	[CNeedOk] "CNeedOk",
	[CHaveErr] "CHaveErr",
	[CReadErr] "CReadErr",
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
static int	sendmsg(Fsstate*, void*, uint*, void*, int);
static int	seterr(Fsstate *, char*, ...);
#pragma varargck	argpos seterr 2

static int	
infauthinit(Proto*, Fsstate *fss)
{
	State *s;
	Key *k;
	Keyinfo ki;

	if(findkey(&k, mkkeyinfo(&ki, fss, nil), "%s", fss->proto->keyprompt) != RpcOk)
		return failure(fss, nil);
	setattrs(fss->attr, k->attr);

	s = emalloc(sizeof(State));
	s->key = k;
	s->info = k->priv;

	fss->ps = s;
	fss->phasename = phasenames;
	fss->maxphase = Maxphase;
	fss->phase = CHaveVersion;

	return RpcOk;
}

static void
infauthclose(Fsstate *fss)
{
	State *s;

	s = fss->ps;
	certfree(s->hiscert);
	pkfree(s->hispk);
	mpfree(s->r0);
	mpfree(s->alphar0r1);
	mpfree(s->alphar0);
	mpfree(s->alphar1);
	/* s->info is s->key->priv */
	closekey(s->key);
	free(s);
}

static int
infauthaddkey(Key *k, int before)
{
	fmtinstall('B', mpfmt);
	if((k->priv = keytoauthinfo(k)) == nil) {
		werrstr("malformed key data");
		return -1;
	}
	return replacekey(k, before);
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

static int
infauthwrite(Fsstate *fss, void *va, uint n)
{
	State *s;
	Certificate *alphacert;
	char	*a, *alphabuf;
	long	now;
	int i, r;

	s = fss->ps;
	a = va;
	if(n < 5)
		return toosmall(fss, 5);
	if(a[0] == '!')
		i = strtoul(a+1, nil, 10);
	else
		i = strtoul(a, nil, 10);
	if(i < 0 || n > i+5 || n > sizeof(s->buf))
		return seterr(fss, "bad auth message count");
	if(n < i+5)
		return toosmall(fss, i+5);
	if(a[0] == '!'){
		r = strlen("remote: ");
		if(i >= ERRMAX-r)
			i = ERRMAX-r-1;
		a += 5;
		if(i >= r && strncmp(a, "remote: ", r) == 0)	/* old implementation sent it */
			r = 0;
		else
			strcpy(s->rerr, "remote: ");
		memmove(s->rerr+r, a, i);
		s->rerr[r+i] = 0;
		return seterr(fss, "failed");	/* acknowledge the error */
	}
	a += 5;
	n = i;
	memmove(s->buf, a, n);
	s->buf[n] = 0;	/* ensure terminator for strtopk etc; size checked above */
	switch(fss->phase) {
	case CNeedVersion:
		s->version = atoi(s->buf);
		if(s->version != 1)
			return seterr(fss, "incompatible authentication protocol");
		fss->phase = CHaveAlphar0;
		return RpcOk;
	case CNeedAlphar1:
		s->alphar1 = strtomp(s->buf, nil, 64, nil);
		if(mpcmp(s->alphar0, s->alphar1) == 0)
			return seterr(fss, "possible replay attack");
		fss->phase = CNeedCert;
		return RpcOk;
	case CNeedCert:
		s->hiscert = strtocert(s->buf);
		if(s->hiscert == nil)
			return seterr(fss, "bad certificate syntax");
		fss->phase = CNeedPk;
		return RpcOk;
	case CNeedPk:
		s->hispk = strtopk(s->buf);
		if(s->hispk == nil)
			return seterr(fss, "bad public key syntax");

		if(verify(s->info->spk, s->hiscert, a, n) == 0)
			return seterr(fss, "pk doesn't match certificate");

		now = time(nil);
		if(s->hiscert->exp != 0 && s->hiscert->exp <= now)
			return seterr(fss, "certificate expired");
		fss->phase = CHaveAlphaCert;
		return RpcOk;
	case CNeedAlphaCert:
		alphacert = strtocert(s->buf);
		if(alphacert == nil)
			return seterr(fss, "bad certificate syntax");

		alphabuf = emalloc(MAXMSG);
		i = mptob64z(s->alphar1, alphabuf, MAXMSG);
		i += mptob64z(s->alphar0, alphabuf + i, MAXMSG - i);
		r = verify(s->hispk, alphacert, alphabuf, i);
		memset(alphabuf, 0, i);
		free(alphabuf);
		certfree(alphacert);
		if(r == 0)
			return seterr(fss, "signature did not match pk");

		if(mpcmp(s->info->p, s->alphar1) <= 0)
			return seterr(fss, "implausible parameter value");

		s->alphar0r1 = mpnew(0);
		mpexp(s->alphar1, s->r0, s->info->p, s->alphar0r1);
		mpfree(s->r0);
		s->r0 = nil;
		mpfree(s->alphar0);
		s->alphar0 = nil;
		mpfree(s->alphar1);
		s->alphar1 = nil;
		fss->phase = CHaveOk;
		return RpcOk;
	case CNeedOk:
		if(n < 2)
			return toosmall(fss, 3);
		if(n != 2 || a[0] != 'O' || a[1] != 'K')
			return RpcOk;		/* skip until OK, error or hangup */

		if(s->failed){
			fss->phase = Broken;
			/* error is in fss->err */
			return RpcOk;
		}
		i = mptobe(s->alphar0r1, nil, MAXMSG, &fss->ai.secret);
		if(i < 0)
			return failure(fss, "internal: can't create secret");
		fss->ai.nsecret = i;
		fss->haveai = 1;
		fss->ai.suid = s->hispk->owner;
		fss->ai.cuid = s->info->mypk->owner;
		fss->phase = Established;
		/* TO DO: add cap when appropriate */
		return RpcOk;
	default:
		return phaseerror(fss, "write");
	}
}

static int
infauthread(Fsstate *fss, void *va, uint *n)
{
	State *s;
	Certificate *alphacert;
	int i;
	char	*a, *buf, *certstr, *pkstr, *alphabuf;
	mpint *p;

	s = fss->ps;
	a = va;

	switch(fss->phase) {
	case CHaveVersion:
		if(sendmsg(fss, a, n, "1", 1))
			return RpcToosmall;
		fss->phase = CNeedVersion;
		return RpcOk;
	case CHaveAlphar0:
		s->r0 = mpnew(0);
		s->alphar0 = mpnew(0);
		buf = emalloc(MAXMSG);

		p = s->info->p;
		mprand(mpsignif(p), genrandom, s->r0);
		mpexp(s->info->alpha, s->r0, p, s->alphar0);
		mptob64z(s->alphar0, buf, MAXMSG);
		i = sendmsg(fss, a, n, buf, strlen(buf));
		free(buf);
		if(i)
			return RpcToosmall;

		fss->phase = CHaveCert;
		return RpcOk;
	case CHaveCert:
		certstr = certtostr(s->info->cert);
		i = sendmsg(fss, a, n, certstr, strlen(certstr));
		free(certstr);
		if(i)
			return RpcToosmall;
		fss->phase = CHavePk;
		return RpcOk;
	case CHavePk:
		pkstr = pktostr(s->info->mypk);
		i = sendmsg(fss, a, n, pkstr, strlen(pkstr));
		free(pkstr);
		if(i)
			return RpcToosmall;
		fss->phase = CNeedAlphar1;
		return RpcOk;
	case CHaveAlphaCert:
		alphabuf = emalloc(MAXMSG);
		i = mptob64z(s->alphar0, alphabuf, MAXMSG);
		i += mptob64z(s->alphar1, alphabuf + i, MAXMSG - i);

		alphacert = sign(s->info->mysk, 0, (uchar*)alphabuf, i);
		memset(alphabuf, 0, i);
		free(alphabuf);

		alphabuf = certtostr(alphacert);
		certfree(alphacert);
		i = sendmsg(fss, a, n, alphabuf, strlen(alphabuf));
		free(alphabuf);
		if(i)
			return RpcToosmall;
		fss->phase = CNeedAlphaCert;
		return RpcOk;
	case CHaveErr:
		if(sendmsg(fss, a, n, fss->err, -strlen(fss->err)))
			return RpcToosmall;
		fss->phase = CNeedOk;
		return RpcOk;
	case CHaveOk:
		if(sendmsg(fss, a, n, "OK", 2))
			return RpcToosmall;
		fss->phase = CNeedOk;
		return RpcOk;
	case CReadErr:
		fss->phase = Broken;
		return failure(fss, "%s", s->rerr);
	default:
		return phaseerror(fss, "read");
	}
}

static int
seterr(Fsstate *fss, char *f, ...)
{
	va_list ap;
	State *s;

	s = fss->ps;
	if(!s->failed){
		va_start(ap, f);
		vsnprint(fss->err, sizeof(fss->err), f, ap);
		va_end(ap);
		s->failed = 1;
	}
	if(s->rerr[0])
		fss->phase = CReadErr;	/* force error to this side after ack */
	else
		fss->phase = CHaveErr;	/* force the error to the other side */
	return RpcOk;
}

static int
sendmsg(Fsstate *fss, void *d, uint *nd, void *s, int ns)
{
	int e;

	e = 0;
	if(ns < 0){
		ns = -ns;
		e = 1;
	}
	if(*nd < ns+5)
		return toosmall(fss, ns+5);
	if(e)
		sprint(d, "!%.3d\n", ns);
	else
		sprint(d, "%.4d\n", ns);
	memmove((char*)d+5, s, ns);
	*nd = ns + 5;
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
	if(n != 0 && (p[1] & 0x80)) {
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
	if(len > 0) {
		*buf = '*';
		return 1;
	}
	return 0;
}

Proto infauth = {
	.name = "infauth",
	.init = infauthinit,
	.write = infauthwrite,
	.read = infauthread,
	.close = infauthclose,
	.addkey = infauthaddkey,
	.closekey = infauthclosekey,
	.keyprompt = "user?",
};
