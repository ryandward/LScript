// expect: the value is String, where Int is declared
type User = { name: String, age: Int }
ann: User = { name: "Ann", age: 42 }
age: Int = ann.name
