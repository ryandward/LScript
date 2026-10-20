// expect: [entry-input]
type Address = { city: String }
type User = { name: String, address: Address }
nameOf: User -> String = (u) => u.name
entry greet: User -> String = nameOf else "?"
