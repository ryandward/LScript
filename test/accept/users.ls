// Closed records as pure data: a literal gives every field once, a read names a declared field, and
// an update is a new record, never a change to the old one.
type User = { name: String, age: Int }
type Person = User
type Team = { lead: Person, size: Int }
type Empty = {}
ann: User = { age: 42, name: "Ann" }
annName: String = ann.name
bob: Person = { ann with name: "Bob" }
team: Team = { lead: bob, size: 2 }
leadName: String = team.lead.name
leadAge: Int = team.lead.age
nothing: Empty = {}
same: User = { ann with }
