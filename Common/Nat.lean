namespace Nat

theorem two_d_coordinate_to_index_lt_size {x y w h: Nat} (h₁ : x < w) (h₂ : y < h) : x + w*y < w*h :=
  Nat.le_pred_of_lt h₂
  |> Nat.mul_le_mul_left w
  |> Nat.add_le_add_iff_right.mpr
  |> (Nat.mul_pred w h).subst (motive :=λx↦w * y + w ≤ x + w)
  |> (Nat.sub_add_cancel (Nat.le_mul_of_pos_right w (Nat.zero_lt_of_lt h₂))).subst
  |> (Nat.add_comm _ _).subst (motive := λx↦x ≤ w*h)
  |> Nat.le_sub_of_add_le
  |> Nat.lt_of_lt_of_le h₁
  |> λx↦(Nat.add_lt_add_right) x (w * y)
  |> (Nat.sub_add_cancel (Nat.le_of_lt ((Nat.mul_lt_mul_left (Nat.zero_lt_of_lt h₁)).mpr h₂))).subst

theorem gt_of_sub_lt {a b c : Nat} (h₁ : a - b < a - c) : c < b := by omega

theorem sub_lt_of_gt {a b c : Nat} (h₁ : b ≤ a) (h₂ : c < b) : a - b < a - c := by omega

theorem lt_of_pred_lt {a b : Nat} (h₁ : a < b.pred) : (a < b) :=
  match b with
  | 0 => h₁
  | _ + 1 => /-(Nat.pred_succ a).substr $-/ Nat.lt_succ_of_lt h₁
