Reduce: module
{
	PATH: con "/dis/lib/spki/reduce.dis";

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

	Token: adt
	{
		x:	int;
		eq:	fn(x: self ref Token, y: ref Token): int;
	};

	init:	fn();

	query:	fn(e: ref Sexprs->Sexp): (string, string);
	record:	fn(top: ref Toplev): string;
};
