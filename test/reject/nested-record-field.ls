// expect: [parse]
type User = { name: String }
type Team = { lead: User }
t: Team = { lead: { name: "Ann" } }
