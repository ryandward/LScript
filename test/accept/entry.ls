// Entries: data comes in as JSON text, is parsed into a fresh frozen value, or gets the failure value.
type User = { name: String, age: Int }
nameOf: User -> String = (u) => u.name
entry greet: User -> String = nameOf else "not a user"
id: User -> User = (u) => u
nobody: User = { name: "nobody", age: 0 }
entry echo: User -> User = id else nobody
ageOf: User -> Int = (u) => u.age
entry age: User -> Int = ageOf else -1
same: Int -> Int = (n) => n
entry number: Int -> Int = same else 0
quote: String -> String = (s) => s
entry text: String -> String = quote else ""
