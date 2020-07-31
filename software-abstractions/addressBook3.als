module tour/addressBook3
open util/ordering [Book]

abstract sig Target {}
sig Addr extends Target {}
abstract sig Name extends Target {}
sig Alias, Group extends Name {}

sig Book {
	names: set Name,
	addr: names -> some Target }
	{
	no n: Name | n in n.^addr
	all a: Alias | lone a.addr
	}

pred add (b,b':Book, n: Name, t:Target) {
	t in Addr or some lookup [b,t]
	b'.addr = b.addr + n -> t
	}

pred del (b,b':Book, n: Name, t:Target) {
	no b.addr.n or some n.(b.addr) - t
	b'.addr = b.addr - n -> t
	}

fun lookup (b: Book, n: Name): set Addr {
	n.^(b.addr) & Addr
	}

pred init (b: Book) {no b.addr}
fact traces {
	init [first]
	all b: Book - last | let b' = next [b] |
		some n: Name, t: Target | add [b,b',n,t] or del [b,b',n,t]
	}

pred show {}
run show for 4

assert lookupYields {
	all b: Book, n: b.names | some lookup [b,n]
	}

check lookupYields for 3 but 4 Book
check lookupYields for 6
