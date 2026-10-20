// expect: [atom-type]
type User = { name: String, age: Int }
type Pet = { name: String, age: Int }
rex: Pet = { name: "Rex", age: 3 }
u: User = rex
