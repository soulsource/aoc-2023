/- This file contains various parsing helpers. Started _after_ Day10. -/

import Common.List
import Common.Nat

namespace Parsing

structure MaybeEmptyRectangularGrid (Element : Type) where
  width : Nat
  height : Nat
  elements : Array Element
  size_valid : elements.size = width * height

instance : Inhabited (MaybeEmptyRectangularGrid Element) where
  default := { width := 0, height := 0, elements := Array.empty, size_valid := rfl}

structure RectangularGrid (Element : Type) extends MaybeEmptyRectangularGrid Element where
  not_empty : width > 0 ∧ height > 0

structure RectangularGrid.Coordinate (grid : RectangularGrid Element) where
  x : Fin grid.width
  y : Fin grid.height

instance {grid : RectangularGrid Element} : BEq grid.Coordinate where
  beq := λa b ↦ a.x == b.x && a.y == b.y

instance {grid : RectangularGrid Element} : Hashable grid.Coordinate where
  hash := λa ↦ Hashable.hash (a.x, a.y)

instance : ToString (RectangularGrid.Coordinate grid) where
  toString := λx ↦ s!"x: {x.x}/{grid.width}, y : {x.y}/{grid.height}"

def RectangularGrid.Coordinate.toIndex {grid : RectangularGrid Element} (coordinate : grid.Coordinate) : Fin (grid.width * grid.height) :=
  ⟨coordinate.x + grid.width * coordinate.y, Nat.two_d_coordinate_to_index_lt_size coordinate.x.isLt coordinate.y.isLt⟩

def RectangularGrid.Coordinate.ofIndex {grid : RectangularGrid Element} (index : Fin (grid.width * grid.height)) : grid.Coordinate :=
  have : grid.width > 0 :=
    have := index.isLt
    match h : grid.width with
    | Nat.zero => absurd ((Nat.zero_mul grid.height).subst (h.subst (motive := λx↦index<x*grid.height) this)) (Nat.not_lt_zero index.val)
    | Nat.succ ww => Nat.succ_pos ww
  {
    x := ⟨index.val % grid.width, Nat.mod_lt index.val this⟩
    y := ⟨index.val / grid.width, Nat.div_lt_of_lt_mul index.isLt⟩
  }

theorem RectangularGrid.Coordinate.toIndex_inv_fromIndex {grid : RectangularGrid Element} (index : Fin (grid.width * grid.height)) : RectangularGrid.Coordinate.toIndex (RectangularGrid.Coordinate.ofIndex index) = index := by
  simp only [RectangularGrid.Coordinate.toIndex, RectangularGrid.Coordinate.ofIndex, Nat.mod_add_div, Fin.eta]

def RectangularGrid.Get {grid : RectangularGrid Element} (coordinate : grid.Coordinate) : Element :=
  grid.elements[coordinate.toIndex]'(grid.size_valid.substr coordinate.toIndex.isLt)

instance : GetElem (RectangularGrid Element) (RectangularGrid.Coordinate grid) Element (λg _ ↦ g = grid) where
  getElem := λ g c h ↦ g.Get (h▸c)

def RectangularGrid.set {grid : RectangularGrid Element} (coordinate : grid.Coordinate) (value : Element) : RectangularGrid Element :=
  let index := (Fin.cast grid.size_valid.symm coordinate.toIndex)
  {
    grid with
      elements := grid.elements.set index value
      size_valid := (grid.elements.size_set index value).substr grid.size_valid
  }

theorem RectangularGrid.set_same_size {grid : RectangularGrid Element} (coordinate : grid.Coordinate) (value : Element) : (grid.set coordinate value).width = grid.width ∧ (grid.set coordinate value).height = grid.height :=
  ⟨rfl,rfl⟩

instance [ToString Element] : ToString (MaybeEmptyRectangularGrid Element) where
  toString := λe ↦ Id.run do
    let mut r := s!"Width: {e.width}, Height: {e.height}"
    for h₂ : y in [0:e.height] do
      r := r.push '\n'
      for h₁ : x in [0:e.width] do
        have : x + e.width *y < e.elements.size := by
          simp[Membership.mem, inferInstance, Std.instMembershipNatRange] at h₁ h₂
          rw[e.size_valid]
          exact Nat.two_d_coordinate_to_index_lt_size h₁ h₂
        r := r ++ (ToString.toString e.elements[x+e.width*y])
    r

instance [ToString Element] : ToString (RectangularGrid Element) where
  toString := ToString.toString ∘ RectangularGrid.toMaybeEmptyRectangularGrid

inductive RectangularGrid.ParseError (ParseCharError : Type)
| NoInput : RectangularGrid.ParseError ParseCharError
| NotRectangular : RectangularGrid.ParseError ParseCharError
| CharacterParsingError : ParseCharError → RectangularGrid.ParseError ParseCharError

instance [ToString ParseCharError] : ToString (RectangularGrid.ParseError ParseCharError) where
  toString := λ
  | .NoInput => "No input provided."
  | .NotRectangular => "Input is not rectangular."
  | .CharacterParsingError e => ToString.toString e

/-- Internal helper. Not private so it's usable in proofs. You probably want ofSubstring instead. -/
protected def RectangularGrid.parseSingleLine (parseCharacter : Char → Except ParseCharError Element) (alreadyParsed : Array Element) (remainingLine : Substring) : Except (RectangularGrid.ParseError ParseCharError) (Array Element) :=
  if _h₁ : remainingLine.isEmpty then
    Except.ok alreadyParsed
  else
    let c := remainingLine.front
    match parseCharacter c with
    | Except.error e => Except.error $ RectangularGrid.ParseError.CharacterParsingError e
    | Except.ok element =>
      RectangularGrid.parseSingleLine parseCharacter (alreadyParsed.push element) (remainingLine.drop 1)
termination_by remainingLine.bsize
decreasing_by
  simp_wf
  simp only [Substring.isEmpty, Substring.bsize, Nat.sub_eq, beq_iff_eq] at _h₁
  simp only [Substring.drop, Substring.bsize, Substring.nextn, Substring.next, String.Pos.add_byteIdx, Nat.sub_eq]
  split
  case isTrue h₂ =>
    simp[←(congrArg String.Pos.byteIdx h₂)] at _h₁
  case isFalse h₂ =>
    simp[String.next, Char.utf8Size]
    split <;> try split <;> try split
    all_goals omega

/-- Internal helper. Not private so it's usable in proofs. You probably want ofSubstring instead. -/
protected def RectangularGrid.parseLines (parseCharacter : Char → Except ParseCharError Element) (alreadyParsed : MaybeEmptyRectangularGrid Element) (remainingLines : List Substring) : Except (RectangularGrid.ParseError ParseCharError) (RectangularGrid Element) :=
  match remainingLines with
  | [] =>
    if h₁ : alreadyParsed.width = 0 ∨ alreadyParsed.height = 0 then
      Except.error RectangularGrid.ParseError.NoInput
    else
      Except.ok {alreadyParsed with not_empty := ⟨Nat.pos_of_ne_zero (not_or.mp h₁).left, Nat.pos_of_ne_zero (not_or.mp h₁).right⟩}
  | l :: ls =>
    let currentSize := alreadyParsed.elements.size
    match RectangularGrid.parseSingleLine parseCharacter alreadyParsed.elements l with
    | Except.error e =>
      Except.error e
    | Except.ok elements =>
      let newSize := elements.size
      if alreadyParsed.height = 0 then -- first line
        RectangularGrid.parseLines parseCharacter {
          width := newSize
          height := 1
          elements
          size_valid := (Nat.mul_one _).substr rfl
        } ls
      else
        if h₂ : newSize = currentSize + alreadyParsed.width then
          RectangularGrid.parseLines parseCharacter {
            width := alreadyParsed.width
            height := alreadyParsed.height + 1
            elements
            size_valid :=
              alreadyParsed.size_valid.subst (motive := λx↦_=x+_) h₂
              |> (Nat.mul_succ (alreadyParsed.width) (alreadyParsed.height)).substr
          } ls
        else
          Except.error RectangularGrid.ParseError.NotRectangular

def RectangularGrid.ofSubstring (parseCharacter : Char → Except ParseCharError Element) (input : Substring) : Except (RectangularGrid.ParseError ParseCharError) (RectangularGrid Element) :=
  let input := input.trim
  let lines := input.splitOn "\n"
  let lines := lines.map Substring.trim
  let lines := lines.filter $ not ∘ Substring.isEmpty
  RectangularGrid.parseLines parseCharacter Inhabited.default lines

def RectangularGrid.ofString (parseCharacter : Char → Except ParseCharError Element) (input : String) : Except (RectangularGrid.ParseError ParseCharError) (RectangularGrid Element) :=
  ofSubstring parseCharacter input.toSubstring
