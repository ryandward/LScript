// expect: the value is Pet, where User is declared
type User = { name: String, age: Int }
type Pet = { name: String, age: Int }
rex: Pet = { name: "Rex", age: 3 }
u: User = rex
