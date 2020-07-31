module tour/addressBook2

abstract sig Target {}
sig Addr extends Target {}
abstract sig Name extends Target {}

sig Alias, Group extends Name {}
// changed from signature to signature fact below
//sig Book {addr: Name -> Target}

// fact below written as signature facts
// applies to every member of  signature
// implicit reference and quantification to particular members
sig Book {
	names: set Name,
	addr: names -> some Target }
	{
	no n: Name | n in n.^addr
	all a: Alias | lone a.addr
	}

pred add (b,b':Book, n: Name, t:Target) {b'.addr = b.addr + n -> t}
pred del (b,b':Book, n: Name, t:Target) {b'.addr = b.addr - n -> t}
fun lookup (b: Book, n: Name): set Addr{n.^(b.addr) & Addr}

assert delUndoesAdd {
	all b, b', b'': Book, n: Name, t: Target |
		no n.(b.addr) and 
		add [b,b',n,t] and del [b',b'',n,t] implies b.addr = b''.addr
	}

check delUndoesAdd for 3

assert addIdempotent {
	all b,b',b'': Book, n: Name, a: Addr |
		add [b,b',n,a] and add [b',b'',n,a] implies b'.addr = b''.addr
	}

check addIdempotent for 3

assert addLocal {
	all b,b': Book, n,n': Name, a: Addr |
		add [b,b',n,a] and n != n' 
		implies lookup [b,n'] = lookup [b',n']
	}

check addLocal for 3 but 2 Book

// x.r: navigation from object x through one application of relation r
// x.^r: navigation from object x through one or more applications of r
//fact {
//	all b: Book | no n: Name | n in n.^(b.addr)
//	}

assert lookupYields {
	all b: Book, n: b.names | some lookup [b,n]
	}

check lookupYields for 4 but 1 Book

// group now contains two addresses
// due to the modifcation of sig to sig fact above for Book
// desired outcome: an alias mapped to two addresses
//pred show (b: Book) {some b.addr}
//pred show (b: Book) {some Alias.(b.addr)}
//run show for 3 but 1 Book
