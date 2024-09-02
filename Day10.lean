import «Common»

namespace Day10

structure Coordinate (width : Nat) (height : Nat) where
  x : Fin width
  y : Fin height

def Coordinate.toIndex {w h : Nat} (c : Coordinate w h) : Fin (w*h) :=
  Fin.mk (c.x.val * c.y.val) (Nat.mul_lt_mul_of_lt_of_lt c.x.isLt c.y.isLt)

def Coordinate.fromIndex {w h : Nat} (index : Fin (w*h)) : Coordinate w h :=
  have : w > 0 :=
    have := index.isLt
    match w with
    | Nat.zero => absurd ((Nat.zero_mul h).subst this) (Nat.not_lt_zero index.val)
    | Nat.succ ww => Nat.succ_pos ww
  {
    x := ⟨index.val % w, Nat.mod_lt index.val this⟩
    y := ⟨index.val / w, Nat.div_lt_of_lt_mul index.isLt⟩
  }

inductive Pipe
| NS : Pipe
| WE : Pipe
| NE : Pipe
| ES : Pipe
| SW : Pipe
| WN : Pipe
deriving BEq

inductive Tile
| pipe : Pipe → Tile
| ground : Tile
| start : Tile
deriving BEq

-- The invariants are maybe overdoing it a bit, but (in the voice of king Leonidas) "This is Lean4!"
structure Area where
  width : Nat
  height : Nat
  start : Coordinate width height
  fields : Array Tile
  size_invariant : fields.size = width * height
  start_invariant : fields[start.toIndex] = Tile.start
  start_invariant2 : ∀ (index : Fin (width*height)), (index ≠ start.toIndex) → fields[index] ≠ Tile.start

inductive Area.ParseError
| NoInput
| UnexpectedCharacter
| NoStart
| MoreThanOneStart
| NotRectangular

private structure Area.Raw where
  width : Nat
  height : Nat
  start : Nat
  fields : Array Tile

private def Area.ParseRaw (input : String) : Except Area.ParseError Area.Raw := do
  let lines := input.splitTrim (· == '\n')
  -- Treat the first line special. We use it to establish width
  match lines with
  | [] => throw Area.ParseError.NoInput
  | l :: ls =>
    let mut width := 0
    let mut arr : Array Tile := Array.empty
    let mut start : Option Nat := none
    for c in l.toSubstring do
      let tile ← parse_character c |> Option.toExcept Area.ParseError.UnexpectedCharacter
      arr := arr.push tile
      if tile == Tile.start then
        if start.isNone then
          start := some width
        else
          throw Area.ParseError.MoreThanOneStart
      width := width + 1
    let mut height := 1
    for line in ls do
      let mut thisWidth := 0
      for c in line.toSubstring do
        let tile ← parse_character c |> Option.toExcept Area.ParseError.UnexpectedCharacter
        arr := arr.push tile
        if tile == Tile.start then
          if start.isNone then
            start := some (thisWidth * height)
          else
            throw Area.ParseError.MoreThanOneStart
        thisWidth := thisWidth +1
      height := height + 1
      if thisWidth != width then
        throw Area.ParseError.NotRectangular
    if let some s := start then
      return {
        width := width,
        height := height,
        start := s,
        fields := arr
      }
    else
      throw Area.ParseError.NoStart
where
  parse_character : Char → Option Tile := λ c ↦ match c with
  | '|' => some $ Tile.pipe Pipe.NS
  | '-' => some $ Tile.pipe Pipe.WE
  | 'L' => some $ Tile.pipe Pipe.NE
  | 'J' => some $ Tile.pipe Pipe.WN
  | '7' => some $ Tile.pipe Pipe.SW
  | 'F' => some $ Tile.pipe Pipe.ES
  | 'S' => some Tile.start
  | '.' => some Tile.ground
  | _ => none
