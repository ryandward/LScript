// expect: [literal-distinct]
type User = { name: String, age: Int }
ann: User = { name: "Ann", age: 1, age: 2 }
