// expect: [entry-ok-type]
type User = { name: String, age: Int }
len: String -> Int = (s) => 0
entry h: User -> Int = len else 0
