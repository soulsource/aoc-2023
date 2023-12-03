namespace Char

def asDigit (d : Char) (ok : Char.isDigit d = true) : Nat :=
  d.toNat - 48
