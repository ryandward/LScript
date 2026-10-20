// expect: User has no field admin
type User = { name: String, age: Int }
ann: User = { name: "Ann", age: 42, admin: 1 }
