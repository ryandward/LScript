// expect: [update-distinct]
type User = { name: String, age: Int }
ann: User = { name: "Ann", age: 42 }
bob: User = { ann with name: "a", name: "b" }
