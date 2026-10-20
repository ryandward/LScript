// `type` and `with` are keywords only where the grammar puts them, and a field label may be any
// identifier JavaScript allows as a property name, reserved words included.
type: Int = 1
type type = Int
type Click = { type: String, class: String, default: Int, with: Int }
e: Click = { type: "click", class: "button", default: 0, with: 2 }
kind: String = e.type
cls: String = e.class
n: type = e.default
e2: Click = { e with type: "dblclick" }
again: type = type
