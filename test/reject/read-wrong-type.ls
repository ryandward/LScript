// expect: [read-type]
type User = { name: String, age: Int }
ann: User = { name: "Ann", age: 42 }
age: Int = ann.name
