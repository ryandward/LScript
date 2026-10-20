// expect: [parse]
type User = { name: String }
u: User = { name: "Ann" }
v: User = { name: u.name }
