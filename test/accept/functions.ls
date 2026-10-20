// Functions take one argument, curried, and stay inside the module: only data is exported.
type User = { name: String, age: Int }
type Rename = String -> User -> User
id: Int -> Int = (x) => x
seven: Int = id(7)
konst: Int -> String -> Int = (x) => (s) => x
three: Int = konst(3)("ignored")
threeOf: String -> Int = konst(3)
alsoThree: Int = threeOf("x")
rename: Rename = (n) => (u) => { u with name: n }
mk: String -> Int -> User = (n) => (a) => { name: n, age: a }
ann: User = mk("Ann")(42)
bob: User = rename("Bob")(ann)
nameOf: User -> String = (u) => u.name
bobName: String = nameOf(bob)
apply: (Int -> Int) -> Int -> Int = (f) => (x) => f(x)
five: Int = apply(id)(5)
base: Int = 10
getBase: String -> Int = (s) => base
ten: Int = getBase("x")
x: Int = 1
shadow: Int -> Int = (x) => x
two: Int = shadow(2)
