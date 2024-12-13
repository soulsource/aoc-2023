def BitVec.setBitTrue {n : Nat} (i : Fin n) (a : BitVec n) : BitVec n :=
  a ||| BitVec.ofNatLt (1 <<< i.val) (by simp[Nat.shiftLeft_eq, i.isLt, Nat.pow_lt_pow_iff_right])

def BitVec.setBitFalse {n : Nat} (i : Fin n) (a : BitVec n) : BitVec n :=
  a &&& BitVec.not (BitVec.ofNatLt (1 <<< i.val) (by simp[Nat.shiftLeft_eq, i.isLt, Nat.pow_lt_pow_iff_right]))

def BitVec.setBit {n : Nat} (i : Fin n) (v : Bool) (a : BitVec n) : BitVec n :=
  if v then
    a.setBitTrue i
  else
    a.setBitFalse i
