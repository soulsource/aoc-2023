namespace Euclid
-- Extended Euclidean algorithm, stolen from Wikipedia.
-- The signature is stolen from Wikipedia too. As in, the values a and b are Nat, but s and t are Int.
def xgcd (a b: Nat) : Nat × Int × Int :=
  if p : b > 0 then
    have : a % b < b := by simp[p, Nat.mod_lt]
    let (d, ss, tt) := xgcd b (a%b)
    (d, tt ,ss - tt * (a / b))
  else
    (a,1,0)
