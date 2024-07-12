namespace Char

def asDigit (d : Char) (_ : Char.isDigit d = true) : Nat :=
  d.toNat - 48
