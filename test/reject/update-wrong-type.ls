// expect: field age of User is Int, and its value is String
type User = { name: String, age: Int }
ann: User = { name: "Ann", age: 42 }
bob: User = { ann with age: "old" }
