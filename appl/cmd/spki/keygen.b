implement Keygen;

include "sys.m";
	sys: Sys;

include "draw.m";

include "keyring.m";
	kr: Keyring;
	IPint, Certificate, PK, SK: import kr;

include "bufio.m";
	bufio: Bufio;
	Iobuf: import bufio;

include "sexprs.m";
	sexprs: Sexprs;
	Sexp: import sexprs;

include "spki.m";
	spki: SPKI;
	Key, Hash: import spki;

include "lists.m";
	lists: Lists;

include "arg.m";

Keygen: module
{
	init:	fn(nil: ref Draw->Context, nil: list of string);
};

init(nil: ref Draw->Context, args: list of string)
{
	sys = load Sys Sys->PATH;
	kr = load Keyring Keyring->PATH;
	bufio = load Bufio Bufio->PATH;
	sexprs = load Sexprs Sexprs->PATH;
	spki = load SPKI SPKI->PATH;
	lists = load Lists Lists->PATH;

	arg := load Arg Arg->PATH;
	arg->init(args);
	arg->setusage("keygen  [-a alg] [-b bits] [-h halg] ... [-s] [-T] [-t 'attr=value attr=value ...']");
	alg := "rsa-pkcs1-sha1";
	tag: string;
	nbits := 1024;
	transport := 0;
	secretonly := 0;
	dohash: list of string;
	while((o := arg->opt()) != 0)
		case o {
		'a' =>
			alg = arg->earg();
		'b' =>
			nbits = int arg->earg();
			if(nbits <= 0)
				arg->usage();
			if(nbits > 4096)
				error("bits must be no greater than 4096");
		'h' =>
			dohash = arg->earg() :: dohash;
		's' =>
			secretonly = 1;
		't' =>
			tag = arg->earg();
		'T' =>
			transport = 1;
		* =>
			arg->usage();
		}
	args = arg->argv();
	if(args != nil)
		arg->usage();
	arg = nil;

	sexprs->init();
	spki->init();

	(ka, enc, ha) := algs(alg);
	if(ka == nil)
		error("invalid algorithm spec: "+alg);
	sk := kr->genSK(ka, ".", nbits);
	if(sk == nil)
		error("unable to generate key: probably unknown algorithm: "+alg);
	if(ha == nil)
		ha = "sha1";
	if(ka == "rsa" && enc == nil)
		enc = "pkcs1";	# it's recommended for RSA
	key := ref Key(kr->sktopk(sk), sk, nbits, ha, enc, nil);
	prexp(key.sexp(), transport);
	if(!secretonly){
		key.sk = nil;
		prexp(key.sexp(), transport);
	}
	for(dohash = lists->reverse(dohash); dohash != nil; dohash = tl dohash){
		h := key.hashexp(hd dohash);
		if(h == nil)
			error("bad hash algorithm: "+hd dohash);
		prexp(h.sexp(), transport);
	}
}

prexp(e: ref Sexp, transport: int)
{
	if(transport)
		a := e.pack();
	else
		a = array of byte (e.text()+"\n");
	if(sys->write(sys->fildes(1), a, len a) != len a)
		error(sys->sprint("write error: %r"));
}

# sig[-enc][-hash]
algs(alg: string): (string, string, string)
{
	(nf, flds) := sys->tokenize(alg, "-");
	if(nf >= 3)
		return (hd flds, hd tl flds, hd tl tl flds);
	if(nf >= 2)
		return (hd flds, nil, hd tl flds);
	if(nf >= 1)
		return (hd flds, nil, nil);
	return (nil, nil, nil);
}

error(s: string)
{
	sys->fprint(sys->fildes(2), "keygen: %s\n", s);
	raise "fail:error";
}
