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

// group now contains two addresses
// due to the modifcation of sig to sig fact above for Book
// desired outcome: an alias mapped to two addresses
//pred show (b: Book) {some b.addr}

pred show (b: Book) {some Alias.(b.addr)}

run show for 3 but 1 Book

// x.r: navigation from object x through one application of relation r
// x.^r: navigation from object x through one or more applications of r
//fact {
//	all b: Book | no n: Name | n in n.^(b.addr)
//	}

assert lookupYields {
	all b: Book, n: b.names | some lookup [b,n]
}

