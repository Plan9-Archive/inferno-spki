implement Speaksfor;

include "sys.m";
	sys: Sys;

include "draw.m";

include "keyring.m";
	kr: Keyring;

include "bufio.m";
	bufio: Bufio;
	Iobuf: import bufio;

include "sexprs.m";
	sexprs: Sexprs;
	Sexp: import sexprs;

include "spki.m";
	spki: SPKI;
	Key, Name, Cert, Valid, Subject, Seqel, Signature, Toplev: import spki;

include "arg.m";

Speaksfor: module
{
	init:	fn(nil: ref Draw->Context, nil: list of string);
};

init(nit: ref Draw->Context, args: list of string)
{
	sys = load Sys Sys->PATH;
	kr = load Keyring Keyring->PATH;
	bufio = load Bufio Bufio->PATH;
	sexprs = load Sexprs Sexprs->PATH;
	spki = load SPKI SPKI->PATH;

	arg := load Arg Arg->PATH;
	arg->init(args);
	arg->setusage("speaksfor [-k] -s subject -i issuer [-t tag] [-b notbefore date]"
			+ " [-a notafter date] [-m keyfs mount point] [-c cert name for keyfs]"
			+ "[-p]");
	mountpoint := "/mnt/keys";
	certname: string = nil;
	subjectname: string = nil;
	issuername: string = nil;
	tagstr := "*";
	infkey := 0;
	v := 0;
	notbefore:string = nil;
	notafter:string = nil;
	printcert := 0;

	while((o := arg->opt()) != 0)
		case o {
		'c' =>
			certname = arg->earg();
		'i' =>
			issuername = arg->earg();
		'k' =>
			infkey = 1;
		'm' =>
			mountpoint = arg->earg();
		'p' =>
			printcert = 1;
		's' =>
			subjectname = arg->earg();
		't' =>
			tagstr = arg->earg();
		'b' =>
			v = 1;
			notbefore = arg->earg();
		'a' =>
			v = 1;
			notafter = arg->earg();
		* =>
			arg->usage();
		}
	
	if(subjectname == nil || issuername == nil)
		arg->usage();

	if(certname == nil)
		certname = subjectname;
	
	if(notafter != nil && notbefore == nil || notbefore != nil && notafter == nil)
		error(sys->sprint("both not-before and not-after dates are required"));
	
	args = arg->argv();
	if(args != nil)
		arg->usage();

	sexprs->init();
	spki->init();

	# Read public and private keys of I
	ikey: ref Key;
	keyfile := issuername;
	if(infkey){
		x := kr->readauthinfo(keyfile);
		if(x == nil)
			error(sys->sprint("can't read authinfo from %s: %r", keyfile));
		ikey = ref Key(x.mypk, x.mysk, 512, "md5", "pkcs1", nil);
	}
	else {
		# keyfile must contain two S-expressions for the public and private keys
		keylist := readexpfile(keyfile);
		if(keylist == nil)
			error(sys->sprint("can't read key file %s", keyfile));

		ikey = spki->parsekey(hd keylist);
		if(ikey == nil)
			error(sys->sprint("can't parse key %s", keyfile));

		keylist = tl keylist;
		ikeytmp := spki->parsekey(hd keylist);
		if(ikeytmp == nil)
			error(sys->sprint("can't parse key %s", keyfile));

		if(ikeytmp.pk != nil)
			ikey.pk = ikeytmp.pk;
		if(ikeytmp.sk != nil)
			ikey.sk = ikeytmp.sk;
	}

	# Read public key of S
	spkexp := (hd readexpfile(mountpoint + "/pk/" + subjectname + "/key"));
	
	# Construct certificate
	valid: ref Valid;
	if(v)
		valid = ref Valid(notbefore, notafter);
	else
		valid = nil;
	tag := ref Sexp.List(ref Sexp.String("tag", nil) :: 
		ref Sexp.List(ref Sexp.String(tagstr, nil) :: nil) ::
		nil);
	issuer := ref Name(ref Key(ikey.pk, nil, ikey.nbits, ikey.halg, ikey.henc, ikey.hash), nil);
	subject := ref Subject.P(spki->parsekey(spkexp));
	if(subject.key == nil)
		error(sys->sprint("can't get subject's public key from file"));
	cert := ref Cert.A(nil, issuer, subject, valid, 1, tag);
	cert.e = cert.sexp();

	# Make signature
	(sig, err) := spki->signcert(cert, "rsa-pkcs1-md5", ikey);
	if(err != nil)
		error(err);

	# Make S-expression from certificate and signature
	seq := ref Seqel.C(cert) :: (ref Seqel.S(sig) :: nil);
	top := ref Toplev.Seq(seq);

	# Either print or add to keyfs
	if(printcert)
		sys->print("%s", top.text());
	else
		writefile(mountpoint + "/new", sys->sprint("%s = %s", certname, top.text()));
}

error(s: string)
{
	sys->fprint(sys->fildes(2), "speaksfor: %s\n", s);
	raise "fail:error";
}

writefile(name: string, s: string)
{
	fd := bufio->open(name, Bufio->OWRITE);
	if(fd == nil)
		error(sys->sprint("can't open %s: %r", name));

	if(fd.write(array of byte s, len s) < len s)
		error(sys->sprint("can't write to %s: %r", name));

	return;
}

readexpfile(name: string): list of ref Sexp
{
	fd := bufio->open(name, Bufio->OREAD);
	if(fd == nil)
		error(sys->sprint("can't open %s: %r", name));

	exp: ref Sexp;
	err: string;
	explist: list of ref Sexp;
	do {
		(exp, err) = Sexp.read(fd);
		if(err != nil)
			error(sys->sprint("invalid s-expression: %s", err));
		if(exp != nil)
			explist = exp :: explist;
	} while(exp != nil);

	return explist;
}
