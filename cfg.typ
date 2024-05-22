#let cfg(it) = {
  show math.equation.where(block: false): it => math.display(it)
  set math.equation(numbering: "(I)")
  it
}
