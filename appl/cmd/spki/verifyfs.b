implement Verifyfs;

include "sys.m";
	sys: Sys;

include "draw.m";

include "bufio.m";

include "keyring.m";
	kr: Keyring;

include "security.m";
	auth: Auth;

include "sexprs.m";
	sexprs: Sexprs;
	Sexp: import sexprs;

include "spki.m";
	spki: SPKI;
	Name, Seqel, Subject, Valid: import spki;

include "arg.m";

Speaksfor: adt {
	subject: ref Subject;
	name: ref Name;
	regarding: ref Sexp;
	valid: ref Valid;
};

Verifierclient: adt {
	fid: int;
	claim: ref Speaksfor;
};

verifier: Verifier;
fids: list of ref Verifierclient;

Verifyfs: module
{
	init: fn (ctxt: ref Draw->Context, nil: list of string);
};

init(ctxt: ref Draw->Context, args: list of string)
{
	sys = load Sys Sys->PATH;

	sexprs = load Sexprs Sexprs->PATH;
	if(sexprs == nil)
		nomod(Sexprs->PATH);

	spki = load SPKI SPKI->PATH;
	if(spki == nil)
		nomod(SPKI->PATH);

	verifier = load Verifier Verifier->PATH;
	if(verifier == nil)
		nomod(Verifier->PATH);

	kr = load Keyring Keyring->PATH;
	if(kr == nil)
		nomod(Keyring->PATH);

	auth = load Auth Auth->PATH;
	if(auth == nil)
		nomod(Auth->PATH);

	verifier->init();
	spki->init();
	sexprs->init();

	arg := load Arg Arg->PATH;
	if(arg == nil)
		nomod(Arg->PATH);
	arg->init(args);
	arg->setusage("verify [-m mntpt]");

	mountpt := "/mnt/spki";
	while((o := arg->opt()) != 0) {
		case o {
		'm' =>
			mountpt = arg->earg();
		* =>
			usage();
		}
	}

	(ok, d) := sys->stat(mountpt);
	if(ok < 0) {
		if(sys->create(mountpt, Sys->OREAD, Sys->DMDIR|8r775) == nil)
			fatal(sys->sprint("Can't create %s directory: %r", mountpt));
	}
	if(sys->bind("#s", mountpt, Sys->MBEFORE|Sys->MCREATE) < 0)
		fatal(sys->sprint("Can't bind #s on %s: %r", mountpt));
	fio := sys->file2chan(mountpt, "verify");
	if(fio == nil)
		fatal(sys->sprint("Can't create file2chan on %s: %r", mountpt));
	
	spawn server(fio);
}

server(fio: ref Sys->FileIO)
{
	for(;;) {
		alt {
			(nil, data, fid, wc) := <-fio.write =>
				if(wc == nil) {
					cleanfid(fid); 
					continue;
				}

				# See if the S-expression is in transport form
				(s, r, err) := Sexp.unpack(data);

				# If not, assume it is in text form
				if(s == nil) {
					(s, t, err) := Sexp.parse(string data);
					if(err != nil) 
						wc <-= (0, sys->sprint("invalid s-expression: %s", err));
				}

				seq := spki->parseseq(s);

				if(seq == nil) {
					wc <-= (0, "invalid SPKI sequence");
					continue;
				}

				(claim, badel, error) := verifier->verify(seq);
				if(error != nil) {
					if(badel == nil)
						s := "end of sequence";
					else
						s = (hd badel).text();
					wc <-= (0, sys->sprint("invalid SPKI proof: failed to verify at element %#q: %s\n", 
								s, error));
					continue;
				}

				client := ref Verifierclient;
				client.fid = fid;
				client.claim = claim;
				fids = client :: fids;

				wc <-= (len data, nil);

			(offset, count, fid, rc) := <-fio.read =>
				if(rc == nil) {
					rc <-= (nil, nil);
					continue;
				}

				client := findfid(fid);

				if(client != nil && client.claim != nil) {

					sai := auth->key("key=default");
					if(sai == nil) {
						rc <-= (nil, sys->sprint("Can't find key: %r\n"));
						continue;
					}

					mysk := kr->genSKfromPK(sai.spk, user());
					mypk := kr->sktopk(mysk);

					pkbuf := array of byte kr->pktostr(mypk);
					state := kr->sha1(pkbuf, len pkbuf, nil, nil);
					cert := kr->sign(sai.mysk, 0, state, "sha1");
					rc <-= (array of byte kr->certtostr(cert), nil);
				}
				else
					rc <-= (nil, "No valid proof was received");
		}
	}
}

user(): string
{
	fd := sys->open("/dev/user", Sys->OREAD);
	if(fd == nil)
		fatal(sys->sprint("Can't open /dev/user: %r"));

	buf := array[Sys->NAMEMAX] of byte;
	n := sys->read(fd, buf, len buf);
	if(n < 0)
		fatal(sys->sprint("error reading /dev/user: %r"));

	return string buf[0:n];
}

findfid(fid: int): ref Verifierclient
{
	for(l := fids; l != nil; l = tl l)
		if((hd l).fid == fid)
			return hd l;

	return nil;
}

cleanfid(fid: int)
{
	ol := fids;
	fids = nil;
	for(; ol != nil; ol = tl ol) {
		c := hd ol;
		if(c.fid != fid)
			fids = c :: fids;
	}
}

nomod(mod: string)
{
	fatal(sys->sprint("Can't load %s: %r", mod));
}

fatal(s: string)
{
	sys->fprint(sys->fildes(2), "verify: %s\n", s);
	raise "fail:error";
}

usage()
{
	sys->fprint(sys->fildes(2), "Usage: verify [-m mountpoint]\n");
	raise "fail:usage";
}
