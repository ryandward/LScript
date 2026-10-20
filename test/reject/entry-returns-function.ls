// expect: [entry-type]
f0: Int -> Int = (x) => x
konst: Int -> Int -> Int = (x) => f0
entry h: Int -> Int -> Int = konst else f0
