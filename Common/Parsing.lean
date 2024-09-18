/- This file contains various parsing helpers. Started _after_ Day10. -/

import Common.List

namespace Parsing

structure RectangularGrid (Element : Type) where
  width : Nat
  height : Nat
  elements : Array Element
  valid : elements.size = width * height

structure RectangularGrid.Coordinate (grid : RectangularGrid Element) where
  x : Fin grid.width
  y : Fin grid.height

private def RectangularGrid.Coordinate.toIndex {grid : RectangularGrid Element} (coordinate : grid.Coordinate) : Fin (grid.width * grid.height) :=
  ⟨coordinate.x + grid.width * coordinate.y,
    Nat.le_pred_of_lt coordinate.y.isLt
    |> Nat.mul_le_mul_left grid.width
    |> Nat.add_le_add_iff_right.mpr
    |> (Nat.mul_pred grid.width grid.height).subst (motive :=λx↦grid.width * coordinate.y.val + grid.width ≤ x + grid.width)
    |> (Nat.sub_add_cancel (Nat.le_mul_of_pos_right grid.width (Nat.zero_lt_of_lt coordinate.y.isLt))).subst
    |> (Nat.add_comm _ _).subst (motive := λx↦x ≤ grid.width*grid.height)
    |> Nat.le_sub_of_add_le
    |> Nat.lt_of_lt_of_le coordinate.x.isLt
    |> λx↦(Nat.add_lt_add_right) x (grid.width * coordinate.y.val)
    |> (Nat.sub_add_cancel (Nat.le_of_lt ((Nat.mul_lt_mul_left (Nat.zero_lt_of_lt coordinate.x.isLt)).mpr coordinate.y.isLt))).subst⟩

private def RectangularGrid.Coordinate.ofIndex (grid : RectangularGrid Element) (index : Fin (grid.width * grid.height)) : grid.Coordinate :=
  have : grid.width > 0 :=
    have := index.isLt
    match h : grid.width with
    | Nat.zero => absurd ((Nat.zero_mul grid.height).subst (h.subst (motive := λx↦index<x*grid.height) this)) (Nat.not_lt_zero index.val)
    | Nat.succ ww => Nat.succ_pos ww
  {
    x := ⟨index.val % grid.width, Nat.mod_lt index.val this⟩
    y := ⟨index.val / grid.width, Nat.div_lt_of_lt_mul index.isLt⟩
  }

theorem Coordinate.toIndex_inv_fromIndex {grid : RectangularGrid Element} (index : Fin (grid.width * grid.height)) : RectangularGrid.Coordinate.toIndex (RectangularGrid.Coordinate.ofIndex grid index) = index := by
  simp only [RectangularGrid.Coordinate.toIndex, RectangularGrid.Coordinate.ofIndex, Nat.mod_add_div, Fin.eta]

def RectangularGrid.Get {grid : RectangularGrid Element} (coordinate : grid.Coordinate) : Element :=
  grid.elements[coordinate.toIndex]'(grid.valid.substr coordinate.toIndex.isLt)

instance : GetElem (RectangularGrid Element) (RectangularGrid.Coordinate grid) Element (λg _ ↦ g = grid) where
  getElem := λ g c h ↦ g.Get (h▸c)

inductive RectangularGrid.ParseError (ParseCharError : Type)
| NoInput : RectangularGrid.ParseError ParseCharError
| NotRectangular : RectangularGrid.ParseError ParseCharError
| CharacterParsingError : ParseCharError → RectangularGrid.ParseError ParseCharError

instance [ToString ParseCharError] : ToString (RectangularGrid.ParseError ParseCharError) where
  toString := λ
  | .NoInput => "No input provided."
  | .NotRectangular => "Input is not rectangular."
  | .CharacterParsingError e => ToString.toString e

def RectangularGrid.parseSingleLine (parseCharacter : Char → Except ParseCharError Element) (alreadyParsed : Array Element) (remainingLine : Substring) : Except (RectangularGrid.ParseError ParseCharError) (Array Element × Nat) :=
  sorry

def RectangularGrid.parseLines (parseCharacter : Char → Except ParseCharError Element) (alreadyParsed : Array Element) (remainingLines : List Substring) : Except (RectangularGrid.ParseError ParseCharError) (Array Element × Nat × Nat) :=
  sorry

def RectangularGrid.ofSubstring (parseCharacter : Char → Except ParseCharError Element) (input : Substring) : Except (RectangularGrid.ParseError ParseCharError) (RectangularGrid Element) :=
  let input := input.trim
  let lines := input.splitOn "\n"
  if h₁ : lines.isEmpty then
    throw RectangularGrid.ParseError.NoInput
  else
    --let height := lines.length
    --let width := lines[0]'(List.not_empty_iff_size_gt_zero.mp $ (Bool.not_eq_true _).mp h₁)
  sorry

def RectangularGrid.ofString (parseCharacter : Char → Except ParseCharError Element) (input : String) : Except (RectangularGrid.ParseError ParseCharError) (RectangularGrid Element) :=
  ofSubstring parseCharacter input.toSubstring
