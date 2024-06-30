
theorem Nat.power_of_two_go_eq_eq (n : Nat) (p : n >0) : Nat.nextPowerOfTwo.go n n p = n := by
  unfold Nat.nextPowerOfTwo.go
  simp_arith

theorem Nat.smaller_smaller_exp {n m o : Nat} (p : o ^ n < o ^ m) (q : o > 0) : n < m :=
  if h₁ : m ≤ n  then
    by have h₂ := Nat.pow_le_pow_of_le_right (q) h₁
       have h₃ := Nat.lt_of_le_of_lt h₂ p
       simp_arith at h₃
  else
    by rewrite[Nat.not_ge_eq] at h₁
       trivial

private theorem mul2_isPowerOfTwo_smaller_smaller_equal (n : Nat) (power : Nat) (h₁ : n.isPowerOfTwo) (h₂ : power.isPowerOfTwo) (h₃ : power < n) : power * 2 ≤ n := by
  unfold Nat.isPowerOfTwo at h₁ h₂
  have ⟨k, h₄⟩ := h₁
  have ⟨l, h₅⟩ := h₂
  rewrite [h₅]
  rewrite[←Nat.pow_succ 2 l]
  rewrite[h₄]
  have h₆ : 2 > 0 := by decide
  apply (Nat.pow_le_pow_of_le_right h₆)
  rewrite [h₅] at h₃
  rewrite [h₄] at h₃
  have h₃ := Nat.smaller_smaller_exp h₃
  simp_arith at h₃
  assumption

private theorem power_of_two_go_one_eq (n : Nat) (power : Nat) (h₁ : n.isPowerOfTwo) (h₂ : power.isPowerOfTwo) (h₃ : power ≤ n) : Nat.nextPowerOfTwo.go n power (Nat.pos_of_isPowerOfTwo h₂) = n := by
  unfold Nat.nextPowerOfTwo.go
  split
  case inl h₄ => exact power_of_two_go_one_eq n (power*2) (h₁) (Nat.mul2_isPowerOfTwo_of_isPowerOfTwo h₂) (mul2_isPowerOfTwo_smaller_smaller_equal n power h₁ h₂ h₄)
  case inr h₄ => rewrite[Nat.not_lt_eq power n] at h₄
                 exact Nat.le_antisymm h₃ h₄
termination_by power_of_two_go_one_eq _ p _ _ _ => n - p
decreasing_by
  simp_wf
  have := Nat.pos_of_isPowerOfTwo h₂
  apply Nat.nextPowerOfTwo_dec <;> assumption

private theorem power_of_two_eq_power_of_two (n : Nat) : n.isPowerOfTwo → (n.nextPowerOfTwo = n) := by
  intro h₁
  unfold Nat.nextPowerOfTwo
  apply power_of_two_go_one_eq
  case h₁ => assumption
  case h₂ => exact Nat.one_isPowerOfTwo
  case h₃ => exact (Nat.pos_of_isPowerOfTwo h₁)

private theorem eq_power_of_two_power_of_two (n : Nat) : (n.nextPowerOfTwo = n) → n.isPowerOfTwo := by
  have h₂ := Nat.isPowerOfTwo_nextPowerOfTwo n
  intro h₁
  revert h₂
  rewrite[h₁]
  intro
  assumption

theorem Nat.power_of_two_iff_next_power_eq (n : Nat) : n.isPowerOfTwo ↔ (n.nextPowerOfTwo = n) :=
  Iff.intro (power_of_two_eq_power_of_two n) (eq_power_of_two_power_of_two n)

theorem Nat.mul2_ispowerOfTwo_iff_isPowerOfTwo (n : Nat) : n.isPowerOfTwo ↔ (2*n).isPowerOfTwo :=
  have h₁ : n.isPowerOfTwo → (2*n).isPowerOfTwo := by
    simp[Nat.mul_comm]
    apply Nat.mul2_isPowerOfTwo_of_isPowerOfTwo
  have h₂ : (2*n).isPowerOfTwo → n.isPowerOfTwo :=
    if h₂ : n.nextPowerOfTwo = n then by
      simp[power_of_two_iff_next_power_eq,h₂]
    else by
      intro h₃
      simp[←power_of_two_iff_next_power_eq] at h₂
      have h₅ := h₃
      unfold Nat.isPowerOfTwo at h₃
      let ⟨k,h₄⟩ := h₃
      cases n with
      | zero => contradiction
      | succ m => cases k with
        | zero => simp_arith at h₄
                  have h₆ (m : Nat) : 2*m+2 > 2^0 := by
                    induction m with
                    | zero => decide
                    | succ o o_ih => simp_arith at *
                                     have h₆ := Nat.le_step $ Nat.le_step o_ih
                                     simp_arith at h₆
                                     assumption
                  have h₆ := Nat.ne_of_lt (h₆ m)
                  simp_arith at h₆
                  rewrite[h₄] at h₆ --why is this needed?!?
                  contradiction
        | succ l => rewrite[Nat.pow_succ 2 l] at h₄
                    rewrite[Nat.mul_comm (2^l) 2] at h₄
                    have h₄ := Nat.eq_of_mul_eq_mul_left (by decide : 0<2) h₄
                    exists l
  Iff.intro h₁ h₂


mutual
  -- intentionally not decidable. This is a logical model, not meant for runtime!
  def Nat.isEven : Nat → Prop
  | .zero => True
  | .succ n => Nat.isOdd n
  -- intentionally not decidable. This is a logical model, not meant for runtime!
  def Nat.isOdd : Nat → Prop
  | .zero => False
  | .succ n => Nat.isEven n
end

theorem Nat.mul_2_is_even {n m : Nat} (h₁ : n = 2 * m) : Nat.isEven n := by
  cases m with
  | zero => simp[Nat.isEven, h₁]
  | succ o => simp_arith at h₁
              simp[Nat.isEven, Nat.isOdd, h₁]
              exact Nat.mul_2_is_even (rfl)

theorem Nat.isPowerOfTwo_even_or_one {n : Nat} (h₁ : n.isPowerOfTwo) : (n = 1 ∨ (Nat.isEven n)) := by
  simp[Nat.isPowerOfTwo] at h₁
  let ⟨k,h₂⟩ := h₁
  cases k with
  | zero => simp_arith[h₂]
  | succ l => rewrite[Nat.pow_succ] at h₂
              rewrite[Nat.mul_comm (2^l) 2] at h₂
              exact Or.inr $ Nat.mul_2_is_even h₂

mutual
  private theorem Nat.not_even_odd {n : Nat} (h₁ : ¬Nat.isEven n) : (Nat.isOdd n) := by
    cases n with
    | zero => unfold Nat.isEven at h₁; contradiction
    | succ o => simp[Nat.isEven, Nat.isOdd] at *
                exact (Nat.not_odd_even (by simp[h₁]))
  private theorem Nat.not_odd_even {n : Nat} (h₁ : ¬Nat.isOdd n) : (Nat.isEven n) := by
    cases n with
    | zero => trivial
    | succ o => simp[Nat.isEven, Nat.isOdd] at *
                exact (Nat.not_even_odd (by simp[h₁]))
end

mutual
  private theorem Nat.even_not_odd {n : Nat} (h₁ : Nat.isEven n) : ¬(Nat.isOdd n ):= by
    cases n with
    | zero => unfold Nat.isOdd; trivial
    | succ o => simp[Nat.isEven, Nat.isOdd] at *
                simp[Nat.odd_not_even h₁]
  private theorem Nat.odd_not_even {n : Nat} (h₁ : Nat.isOdd n) : ¬(Nat.isEven n ):= by
    cases n with
    | zero => contradiction
    | succ o => simp[Nat.isEven, Nat.isOdd] at *
                simp[Nat.even_not_odd h₁]
end

theorem Nat.odd_not_even_odd {n : Nat} : Nat.isOdd n ↔ ¬Nat.isEven n :=
  Iff.intro Nat.odd_not_even Nat.not_even_odd

theorem Nat.even_not_odd_even {n : Nat} : Nat.isEven n ↔ ¬Nat.isOdd n :=
  Iff.intro Nat.even_not_odd Nat.not_odd_even

theorem Nat.pred_even_odd {n : Nat} (h₁ : Nat.isEven n) (h₂ : n > 0) : Nat.isOdd n.pred := by
  cases n with
  | zero => contradiction
  | succ o => simp[Nat.isEven] at h₁
              assumption

theorem Nat.sub_lt_of_lt_add {a b c : Nat} (h₁ : a < c + b) (h₂ : b ≤ a) : a - b < c :=
  have h₃ : a + 1 ≤ c + b := Nat.succ_le_of_lt h₁
  have h₄ := Nat.sub_le_of_le_add h₃
  have h₅ : 1 + a - b ≤ c := (Nat.add_comm a 1).subst (motive := λx ↦ x - b ≤ c) h₄
  have h₆ := Nat.add_sub_assoc h₂ 1
  have h₇ : 1 + (a-b) ≤ c := h₆.subst (motive := λx ↦ x ≤ c) h₅
  have h₈ : (a-b) + 1 ≤ c := (Nat.add_comm 1 (a-b)).subst (motive := λx ↦ x ≤ c) h₇
  Nat.lt_of_succ_le h₈
