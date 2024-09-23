import Common.Nat

namespace Substring

theorem nextn_ge (s : Substring) (n : Nat) (p : String.Pos) : s.nextn n p ≥ p := by
  unfold Substring.nextn
  cases n
  case zero => simp[String.Pos.le_iff]
  case succ nn =>
    simp
    unfold Substring.next
    simp
    if h₁ :s.startPos + p = s.stopPos then
      simp[h₁]
      exact nextn_ge s nn p
    else
      simp[h₁]
      have h₂ : { byteIdx := (s.str.next (s.startPos + p)).byteIdx - s.startPos.byteIdx  : String.Pos} ≤ s.nextn nn { byteIdx := (s.str.next (s.startPos + p)).byteIdx - s.startPos.byteIdx } :=
        nextn_ge _ nn _
      simp[String.Pos.le_iff]
      apply Nat.le_trans  _ h₂
      unfold String.next
      simp[Char.utf8Size]
      split <;> try split <;> try split
      all_goals
      omega

theorem drop_bsize_dec (s : Substring) (n : Nat) (h₁ : ¬s.isEmpty) (h₂ : n ≠ 0) : (s.drop n).bsize < s.bsize := by
  cases n ; contradiction
  case succ nn =>
    simp only [Substring.drop, Substring.bsize, Substring.nextn, Substring.next, String.Pos.add_byteIdx, Nat.sub_eq]
    simp only [Substring.isEmpty, Substring.bsize, Nat.sub_eq, beq_iff_eq] at h₁
    if h₃ : (s.startPos.byteIdx + ({ str := s.str, startPos := s.startPos, stopPos := s.stopPos : Substring}.nextn nn (if s.startPos + 0 = s.stopPos then 0 else { byteIdx := (s.str.next (s.startPos + 0)).byteIdx - s.startPos.byteIdx })).byteIdx) ≤ s.stopPos.byteIdx then
      apply Nat.sub_lt_of_gt; exact h₃
      split
      case h₂.isTrue hx =>
        simp[←hx] at h₁
      case h₂.isFalse h₄ =>
        unfold String.next
        simp
        unfold Char.utf8Size
        simp
        apply Nat.lt_of_lt_of_le _ (nextn_ge { str := s.str, startPos := s.startPos, stopPos := s.stopPos } nn _)
        split <;> try split <;> try split
        all_goals
          simp
          omega
    else
      have h₄ : s.stopPos.byteIdx - (s.startPos.byteIdx + ({ str := s.str, startPos := s.startPos, stopPos := s.stopPos : Substring}.nextn nn (if s.startPos + 0 = s.stopPos then 0 else { byteIdx := (s.str.next (s.startPos + 0)).byteIdx - s.startPos.byteIdx })).byteIdx)  = 0 := by
        omega
      rw[h₄]
      omega
