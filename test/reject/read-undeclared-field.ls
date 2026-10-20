// expect: User has no field email
type User = { name: String, age: Int }
ann: User = { name: "Ann", age: 42 }
email: String = ann.email
