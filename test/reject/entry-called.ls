// expect: [call-type]
id: Int -> Int = (x) => x
entry h: Int -> Int = id else 0
n: Int = h(1)
