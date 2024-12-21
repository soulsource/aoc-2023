import Std.Data.HashSet
import Common.Finite

open Std.HashSet
namespace Std.HashSet

theorem finite_size {α : Type u} [Finite α] [BEq α] [LawfulBEq α] [Hashable α] (set : Std.HashSet α) : set.size ≤ Finite.cardinality α := by

  sorry
