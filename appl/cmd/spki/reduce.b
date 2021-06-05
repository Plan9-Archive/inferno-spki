implement Reduce;

#
# this is an implementation of a variant of
#	``How to Resolve SDSI Names Without Closure'',
#	Sameer Ajmani, MIT Computer Science and AI Lab,
#	28 February 2004
#
# this version is currently just for experiment

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
	Hash, Key, Name, Cert, Subject, Seqel, Signature, Toplev: import spki;

include "encoding.m";
	base16: Encoding;
	base64: Encoding;

include "arg.m";

Reduce: module
{
	init:	fn(nil: ref Draw->Context, nil: list of string);
};

Pair: adt {
	c:	ref Cert;
#	sig:	ref Certificate;
	sig:	ref Signature;
	tag:	string;
};

Proof: adt {
	name:	ref Name;
	subject:	ref Subject;
	seq:	list of ref Pair;

	eq:	fn(p1: self ref Proof, p2: ref Proof): int;
};

mountpoint: string;	# keyfs mountpoint

lookkey(n: string): string
{
	fd := bufio->open(mountpoint + "/pk/" + n + "/key", Bufio->OREAD);
	if(fd == nil) {
		sys->fprint(sys->fildes(2), "can't open %s: %r\n", n);
		return nil;
	}

	(exp, err) := Sexp.read(fd);
	if(err != nil) {
		sys->fprint(sys->fildes(2), "invalid s-expression: %s\n", err);
		return nil;
	}

	return exp.text();
}

init(nil: ref Draw->Context, args: list of string)
{
	sys = load Sys Sys->PATH;
	kr = load Keyring Keyring->PATH;
	bufio = load Bufio Bufio->PATH;
	sexprs = load Sexprs Sexprs->PATH;
	spki = load SPKI SPKI->PATH;
	base16 = load Encoding Encoding->BASE16PATH;
	base64 = load Encoding Encoding->BASE64PATH;
	arg := load Arg Arg->PATH;

	spki->init();
	sexprs->init();
	arg->init(args);

	arg->setusage("reduce [-m keyfs mount point]");
	mountpoint = "/mnt/keys";
	while((o := arg->opt()) != 0)
		case o {
		'm' =>
			mountpoint = arg->earg();
		* =>
			arg->usage();
		}

	f := bufio->fopen(sys->fildes(0), Sys->OREAD);
	while((line := f.gets('\n')) != nil){
		(nf, flds) := sys->tokenize(line, "\n \t");
		if(nf <= 0 || (hd flds)[0] == '#')
			continue;
		if(hd flds == "?"){
			flds = tl flds;
			if(flds == nil)
				continue;
			k0 := lookkey(hd flds);
			if(k0 == nil){
				sys->print("%s: unknown name\n", k0);
				continue;
			}
			n0 := 0;
			while((flds = tl flds) != nil){
				k0 += " "+hd flds;
				n0 = 1;
			}
			if(n0)
				k0 = "(name "+k0+")";
			(e, nil, diag) := Sexp.parse(k0);
			if(e == nil){
				sys->print("invalid expression: %q: %s\n", k0, diag);
				continue;
			}
			query(e);
			continue;
		}
		for(l := flds; l != nil; l = tl l)
			if(hd l == "<-")
				break;
		if(l == nil){
			sys->print("%s: bad map\n", line);
			continue;
		}
		n0 := 0;
		n1 := 0;
		k0 := lookkey(hd flds);
		if(k0 == nil){
			sys->print("%s: unknown name\n", k0);
			continue;
		}
		while((flds = tl flds) != l){
			k0 += " "+hd flds;
			n0 = 1;
		}
		l = tl l;
		if(l == nil){
			sys->print("%s: bad entry\n", line);
			continue;
		}
		k1 := lookkey(hd l);
		if(k1 == nil){
			sys->print("%s: unknown name\n", k1);
			continue;
		}
		while((l = tl l) != nil){
			k1 += " "+hd l;
			n1 = 1;
		}
		if(n0)
			k0 = "(name "+k0+")";
		if(n1)
			k1 = "(name "+k1+")";
		s := "(cert (issuer "+k0+") (subject "+k1+"))";
		#(e, err) := Sexp.read(f);
		#if(e == nil && err == nil)
		#	break;
		(e, nil, err) := Sexp.parse(s);
		if(err != nil){
			sys->fprint(sys->fildes(2), "invalid s-expression %q: %s\n", s, err);
			continue;
		}
		(top, diag) := spki->parse(e);
		if(diag != nil){
			sys->fprint(sys->fildes(2), "invalid spki structure: %s\n", diag);
			continue;
		}
		record(top);
	}
	showall();
	args = tl args;
	for(; args != nil; args = tl args){
		(e, err, nil) := Sexp.parse(hd args);
		if(err != nil){
			sys->fprint(sys->fildes(2), "bad s-expr arg: %s\n", err);
			continue;
		}
		query(e);
	}
}

query(e: ref Sexp)
{
	# NOTE: would reset maps here for incremental queries

	n := spki->parsename(e);
	if(n == nil){
		sys->fprint(sys->fildes(2), "bad name arg\n");
		return;
	}
	un := uname(n);
	sys->print("%s ->\n= %s->\n", n.text(), un.text());
	(pl, diag) := resolve(un);
	if(pl != nil){
		for(; pl != nil; pl = tl pl){
			p := hd pl;
			sys->print("\t%q -> %q\n", p.name.text(), p.subject.text());
		}
	}else if(diag != nil)
		sys->print("\terror [%q]\n", diag);
	else
		sys->print("\tnone\n");
}


#
# return all reducing proofs whose name is n
#
# n must be local; it's possible to extend the function but the
# functionality wouldn't be useful at the moment
#

resolve(n: ref Name): (list of ref Proof, string)
{
	if(!n.islocal())
		return (nil, "non-local name");
	load_value(n);
	return (value(n), nil);
}

loadedvalues: ref Map[ref Name, ref Token];

load_value(n: ref Name)
{
	if(loadedvalues == nil)
		loadedvalues = ref Map[ref Name, ref Token];
	if(!loadedvalues.exists(n)){
		loadedvalues.add(n, ref Token(1));
		for(ps := proofsbyname(n.local()); ps != nil; ps = tl ps)
			insertp(hd ps);
	}
}

#
# return all reducing proofs whose subject is k
#
unresolve(k: ref Key): list of ref Proof
{
	load_reverse(k);
	return reverse(k);
}

loadedcompatibles: ref Map[ref Name, ref Token];

load_compatible(n: ref Name)
{
	if(loadedcompatibles == nil)
		loadedcompatibles = ref Map[ref Name, ref Token];
	if(!loadedcompatibles.exists(n)){
		loadedcompatibles.add(n, ref Token(1));
		for(ps := proofsbysubjprefix(n); ps != nil; ps = tl ps)
			insertp(hd ps);
	}
}

loadedreverse: ref Map[ref Key, ref Token];

load_reverse(k: ref Key)
{
	if(loadedreverse == nil)
		loadedreverse = ref Map[ref Key, ref Token];
	if(!loadedreverse.exists(k)){
		loadedreverse.add(k, ref Token(1));
		for(ps := proofsbysubjkey(k); ps != nil; ps = tl ps)
			insertp(hd ps);
	}
}

reversemap: ref Map[ref Key, ref Proof];

reverse(k: ref Key): list of ref Proof
{
	if(reversemap == nil)
		return nil;
	return reversemap.vals(k);
}

addreverse(k: ref Key, p: ref Proof)
{
	if(reversemap == nil)
		reversemap = ref Map[ref Key, ref Proof];
	reversemap.add(k, p);
}

#
# certificate closure
#

cert2proof(c: ref Cert): ref Proof
{
	return ref Proof(c.issuer, c.subject, ref Pair(c, nil, string tag++) :: nil);
}

insertc(c: ref Cert)
{
	insertp(cert2proof(c));
}

insertp(p: ref Proof)
{
	if(check(p.name, p.subject) == 0){
sys->print("insertp(%s,%s)\n", p.name.text(), p.subject.text());
		putcheck(p.name, p.subject);
		pick s := p.subject {
		N =>
			n := s.name.local();
			addcompatible(n, p);
			load_value(n);
			for(ps := value(n); ps != nil; ps = tl ps)
				insertp(compose(p, hd ps));
		P =>
			addvalue(p.name, p);
			addreverse(p.subject.principal(), p);
			load_compatible(p.name);
			for(ps := compatible(p.name); ps != nil; ps = tl ps)
				insertp(compose(hd ps, p));
			load_reverse(p.name.principal);
		}
	}
}

compose(p1: ref Proof, p2: ref Proof): ref Proof
{
	# p1.subject = p2.name . X, some X
	X: list of string;
	pick p1s := p1.subject {
	P =>
		if(!p1s.key.eq(p2.name.principal))
			raise "invalid composition";
		X = p2.name.names;
	N =>
		if(!p1s.name.isprefix(p2.name))
			raise "invalid composition";
		X = suffixof(p2.name.names, p1s.name.names);
	}
	if(X == nil)
		return ref Proof(p1.name, p2.subject, append(p1.seq, p2.seq));
	pick s := p2.subject {
	P =>
		return ref Proof(p1.name, ref Subject.N(ref Name(s.key, X)), append(p1.seq, p2.seq));
	N =>
		return ref Proof(p1.name, ref Subject.N(ref Name(s.name.principal, append(s.name.names, X))),
			append(p1.seq, p2.seq));
	* =>
		raise "invalid composition";
	}
}

values: ref Map[ref Name, ref Proof];

value(n: ref Name): list of ref Proof
{
	if(values == nil)
		return nil;
	return values.vals(n);
}

addvalue(n: ref Name, p: ref Proof)
{
sys->print("add value %q %q\n", n.text(), p.subject.text());
	if(values == nil)
		values = ref Map[ref Name, ref Proof];
	values.add(n, p);
}

checked: list of (ref Name, ref Subject);

check(n: ref Name, subject: ref Subject): int
{
	for(l := checked; l != nil; l = tl l){
		(cn, cs) := hd l;
		if(n.eq(cn) && cs.eq(subject))
			return 1;
	}
	return 0;
}

putcheck(n: ref Name, subject: ref Subject)
{
	checked = (n, subject) :: checked;
}

compatibles: ref Map[ref Name, ref Proof];

addcompatible(n: ref Name, p: ref Proof)
{
	if(compatibles == nil)
		compatibles = ref Map[ref Name, ref Proof];
	compatibles.add(n, p);
}

compatible(n: ref Name): list of ref Proof
{
	if(compatibles == nil)
		return nil;
	return compatibles.vals(n);
}

Proof.eq(p1: self ref Proof, p2: ref Proof): int
{
	return p1.name.eq(p2.name) && p1.subject.eq(p2.subject);
}

suffixof(s1, s2: list of string): list of string
{
	for(; s1 != nil; s1 = tl s1){
		if(s2 == nil || hd s2 != hd s1)
			return nil;
		s2 = tl s2;
	}
	return s2;
}

append[T](l1, l2: list of T): list of T
{
	rl1: list of T;
	for(; l1 != nil; l1 = tl l1)
		rl1 = hd l1 :: rl1;
	for(; rl1 != nil; rl1 = tl rl1)
		l2 = hd rl1 :: l2;
	return l2;
}

rev[T](l: list of T): list of T
{
	rl: list of T;
	for(; l != nil; l = tl l)
		rl = hd l :: rl;
	return rl;
}

onlist[T](e: T, l: list of T): int for {
	T =>
		eq:	fn(a: self T, b: T): int;
	}
{
	for(; l != nil; l = tl l)
		if(e.eq(hd l))
			return 1;
	return 0;
}

#
# test bed things
#

uniquenames: list of ref Name;

uname(n: ref Name): ref Name
{
	if(n == nil)
		return n;
	n.principal = ukey(n.principal);
	for(ul := uniquenames; ul != nil; ul = tl ul)
		if(n.eq(hd ul))
			return hd ul;
	uniquenames = n :: uniquenames;
	return n;
}

uniquekeys: list of ref Key;

ukey(k: ref Key): ref Key
{
	if(k == nil)
		return k;
sys->print("Key\n");
	for(ul := uniquekeys; ul != nil; ul = tl ul)
		if(k.eq(hd ul))
			return hd ul;
	k.hashexp("md5");
if(k.hash == nil)sys->print("FAILED\n"); else sys->print("HASHED\n");
	uniquekeys = k :: uniquekeys;
	return k;
}

usubject(as: ref Subject): ref Subject
{
	pick s := as {
	P =>
		s.key = ukey(s.key);
	N =>
		s.name = uname(s.name);
	T =>
		nl: list of ref Subject;
		for(l := s.subs; l != nil; l = tl l)
			nl = usubject(hd l) :: nl;
		s.subs = rev(nl);
	}
	return as;
}

certu(c: ref Cert)
{
	pick s := c.subject {
	N =>
		if(s.name.principal == nil)
			s.name.principal = c.issuer.principal;
	}
	c.issuer = uname(c.issuer);
	c.subject = usubject(c.subject);
	pick d := c {
	A =>
		authcerts = d :: authcerts;
	N =>
		namecerts = d :: namecerts;
	}
}

tag := 0;

proofsbyname(n: ref Name): list of ref Proof
{
	# TO DO: fetch proofs whose name is n
	pl: list of ref Proof;
	for(nl := namecerts; nl != nil; nl = tl nl){
		c := hd nl;
		if(n.eq(c.issuer))
			pl = cert2proof(c) :: pl;
	}
sys->print("%s(%d)\n", n.text(), len pl);
	return pl;
}

proofsbysubjprefix(n: ref Name): list of ref Proof
{
	# TO DO: fetch proofs whose subject starts with n
	pl: list of ref Proof;
	for(nl := namecerts; nl != nil; nl = tl nl){
		c := hd nl;
		pick s := c.subject {
		P =>
			if(n.names == nil && n.principal.eq(s.key))	# can it happen?
				pl = cert2proof(c) :: pl;
		N =>
			if(n.isprefix(s.name))
				pl = cert2proof(c) :: pl;
		}
	}
	return nil;
}

proofsbysubjkey(k: ref Key): list of ref Proof
{
	# TO DO: fetch proofs whose subject is k
	pl: list of ref Proof;
	for(nl := namecerts; nl != nil; nl = tl nl){
		c := hd nl;
		pick s := c.subject {
		P =>
			if(s.key.eq(k))
				pl = cert2proof(c) :: pl;
		}
	}
	return pl;
}

namecerts: list of ref Cert.N;
authcerts: list of ref Cert.A;
sigs: list of ref Signature;
pubkeys: list of ref Key;
#proofs: list of (ref Name, ref Subject, list of ref Seqel);

record(top: ref Toplev)
{
	pick t := top {
	C =>
		c := t.v;
		certu(c);
		sys->print("cert: %s\n", c.text());
	Sig =>
		sys->print("got signature %q\n", t.v.text());
		t.v.key = ukey(t.v.key);
		sigs = t.v :: sigs;
	K =>
		sys->print("got key %q\n", t.v.text());
		ukey(t.v);
		pubkeys = uniquekeys;
	Seq =>
		els := t.v;
		if(len els < 2){
			sys->print("bad sequence\n");
			return;
		}
		pick e0 := hd els {
		O =>
			# ("do" "prove" name subject)
		* =>
			sys->print("not a proof sequence\n");
		}
	* =>
		sys->print("unexpected spki type\n");
	}
}

showall()
{
	sys->print("name certs:\n");
	for(nl := namecerts; nl != nil; nl = tl nl)
		sys->print("\t%s\n", (hd nl).text());
	sys->print("auth certs:\n");
	for(al := authcerts; al != nil; al = tl al)
		sys->print("\t%s\n", (hd al).text());
	sys->print("pub keys:\n");
	for(pl := pubkeys; pl != nil; pl = tl pl)
		sys->print("\t%s\n", (hd pl).text());
	sys->print("sigs:\n");
	for(sl := sigs; sl != nil; sl = tl sl)
		sys->print("\t%s\n", (hd sl).text());
}

Mapel: adt[K,V] for {
	K =>
		eq:	fn(a: self K, b: K): int;
	V =>
		eq:	fn(a: self V, b: V): int;
	}
{
	k:	K;
	vs:	list of V;
};

Map: adt[K, V] for {
	K =>
		eq:	fn(a: self K, b: K): int;
	V =>
		eq:	fn(a: self V, b: V): int;
	}
{
	mem:	list of ref Mapel[K,V];

	reset:	fn(m: self ref Map[K,V]);
	entry:	fn(m: self ref Map[K,V], k: K, insert: int): ref Mapel[K,V];
	exists:	fn(m: self ref Map[K,V], k: K): int;
	key:	fn(m: self ref Map[K,V], k: K): K;
	vals:	fn(m: self ref Map[K,V], k: K): list of V;
	add:	fn(m: self ref Map[K,V], k: K, v: V);
};

Map[K,V].reset(m: self ref Map[K,V])
{
	m.mem = nil;
}

Map[K,V].entry(m: self ref Map[K,V], k: K, insert: int): ref Mapel[K,V]
{
	for(l := m.mem; l != nil; l = tl l){
		e := hd l;
		if(k.eq(e.k))
			return e;
	}
	if(insert){
		e := ref Mapel[K,V](k, nil);
		m.mem = e :: m.mem;
		return e;
	}
	return nil;
}

Map[K,V].key(m: self ref Map[K,V], k: K): K
{
	if((e := m.entry(k, 0)) != nil)
		return e.k;
	return k;
}

Map[K,V].exists(m: self ref Map[K,V], k: K): int
{
	return m.entry(k, 0) != nil;
}

Map[K,V].vals(m: self ref Map[K,V], k: K): list of V
{
	if((e := m.entry(k, 0)) != nil)
		return e.vs;
	return nil;
}

Map[K,V].add(m: self ref Map[K,V], k: K, v: V)
{
	e := m.entry(k, 1);
	if(!onlist(v, e.vs))
		e.vs = v :: e.vs;
}

Token: adt
{
	x:	int;
	eq:	fn(x: self ref Token, y: ref Token): int;
};

Token.eq(x: self ref Token, y: ref Token): int
{
	return x.x == y.x;
}
