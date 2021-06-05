implement Sign;

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
	Key, Name, Cert, Subject, Seqel, Signature, Toplev: import spki;

include "lists.m";
	lists: Lists;

include "arg.m";

Sign: module
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
	arg->setusage("sign [-hk] private-key sexp-file ...");
	infkey := 0;
	dohash := 1;
	plainexp := 0;
	while((o := arg->opt()) != 0)
		case o {
		'e' =>	plainexp = 1;
		'h' =>	dohash = 0;
		'k' =>	infkey = 1;
		* =>		arg->usage();
		}
	args = arg->argv();
	if(args == nil)
		arg->usage();
	keyorfile := hd args;
	args = tl args;
	if(args == nil)
		arg->usage();
	arg = nil;

	sexprs->init();
	spki->init();
	key: ref Key;
	if(infkey){
		x := kr->readauthinfo(keyorfile);
		if(x == nil)
			error(sys->sprint("can't read authinfo from %s: %r", keyorfile));
		key = ref Key(x.mypk, x.mysk, 512, "md5", "pkcs1", nil);	# TO DO: key length
	}else{
		ekey := readexp(keyorfile);
		key = spki->parsekey(ekey);
		if(key == nil)
			error(sys->sprint("can't parse key %s", keyorfile));
	}
	if(key.sk == nil)
		error("missing private key");
	seq: list of ref Seqel;
	for(; args != nil; args = tl args){
		exp := readexp(hd args);
		(item, diag) := spki->parse(exp);
		if(diag != nil)
			error(sys->sprint("%s: %s", hd args, diag));
		sig: ref Signature;
		serr: string;
		pick r := item {
		C =>
			cert := r.v;
			(sig, serr) = spki->signcert(cert, "rsa-pkcs1-md5", key);
			if(1 && sig != nil){		# check that the key worked
				cerr := spki->checksig(cert, sig);
				if(cerr != nil)
					error(sys->sprint("signature check error: %s", cerr));
			}
			seq = ref Seqel.C(cert) :: seq;
		* =>
			seq = ref Seqel.E(exp) :: seq;
			(sig, serr) = spki->signbytes(exp.pack(), "rsa1-pkcs1-md5", key);
		}
		seq = ref Seqel.S(sig) :: seq;
	}
	top := ref Toplev.Seq(lists->reverse(seq));
	sys->print("%s\n", top.text());
}

readexp(s: string): ref Sexp
{
	(e, err) := Sexp.read(openexp(s));
	if(err != nil)
		error(sys->sprint("invalid s-expression %s: %s", s, err));
	return e;
}

openexp(s: string): ref Bufio->Iobuf
{
	if(s != nil && (s[0] == '(' || s[0] == '{'))
		return bufio->sopen(s);	# direct s-expression or base64-encoded transport form
	f := bufio->open(s, Bufio->OREAD);
	if(f == nil)
		error(sys->sprint("can't open %s: %r", s));
	return f;
}

error(s: string)
{
	sys->fprint(sys->fildes(2), "sign: %s\n", s);
	raise "fail:error";
}
