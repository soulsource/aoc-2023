import «Common»
import «BinaryHeap»

namespace Day11

inductive Pixel
| void
| galaxy

instance : ToString Pixel where
  toString := λ
  | .void => "."
  | .galaxy => "#"

structure ParseCharError where
  foundChar : Char

instance : ToString ParseCharError where
  toString := λx ↦ s!"Invalid character. Expected '#' or '.', but found {x.foundChar}"

def parseCharacter : Char → Except ParseCharError Pixel
| '.' => Except.ok Pixel.void
| '#' => Except.ok Pixel.galaxy
| foundChar => Except.error {foundChar}

abbrev TelescopePicture := Parsing.RectangularGrid Pixel
abbrev PixelPos := Parsing.RectangularGrid.Coordinate (Element := Pixel)

------------------------------------------------------------------------------------------

def galaxies (p : TelescopePicture) : List (PixelPos p) :=
  let rec worker := λ(index : Fin (p.width * p.height)) ↦
    match p.elements[index]'(p.size_valid.substr index.isLt) with
    | .void =>
      if h : index + 1 < p.width * p.height then
        worker ⟨index + 1, h⟩
      else
        []
    | .galaxy =>
      (Parsing.RectangularGrid.Coordinate.ofIndex index) ::
        if h : index + 1 < p.width * p.height then
          worker ⟨index + 1, h⟩
        else
          []
  worker ⟨0,Nat.mul_pos p.not_empty.left p.not_empty.right⟩

private def sortGalaxiesByRow (a b : PixelPos p) : Bool :=
  a.y ≤ b.y

private def sortGalaxiesByRow_wellDefinedLE : BinaryHeap.TotalAndTransitiveLe (sortGalaxiesByRow (p := picture)) := by
  unfold sortGalaxiesByRow
  unfold BinaryHeap.TotalAndTransitiveLe BinaryHeap.transitive_le BinaryHeap.total_le
  simp only [decide_eq_true_eq, and_imp]
  constructor
  omega
  omega

private def sortGalaxiesByColumn (a b : PixelPos p) : Bool :=
  a.x ≤ b.x

private def sortGalaxiesByColumn_wellDefinedLE : BinaryHeap.TotalAndTransitiveLe (sortGalaxiesByColumn (p := picture)) := by
  unfold sortGalaxiesByColumn
  unfold BinaryHeap.TotalAndTransitiveLe BinaryHeap.transitive_le BinaryHeap.total_le
  simp only [decide_eq_true_eq, and_imp]
  constructor
  omega
  omega

/-- Output is from highest to lowest index! -/
def horizontalVoids (galaxies : List (PixelPos p)) : List (Fin p.height) :=
  let rec worker : {n : Nat} → List (Fin p.height)→ Fin p.height → BinaryHeap (PixelPos p) sortGalaxiesByRow n → List (Fin p.height) := λ {n : Nat} previous currentIndex remainingGalaxies ↦
    match n with
    | 0 => previous
    | _+1 =>
      let next := remainingGalaxies.tree.root'
      if h : currentIndex < next.y then
        have : currentIndex + 1 < p.height := Nat.lt_of_le_of_lt (Nat.succ_le.mpr h) next.y.isLt
        worker (currentIndex :: previous) ⟨currentIndex + 1,this⟩ remainingGalaxies
      else if h₂ : currentIndex = next.y ∧ currentIndex + 1 < p.height then
        worker previous ⟨currentIndex+1, h₂.right⟩ (remainingGalaxies.pop.snd)
      else
        worker previous currentIndex (remainingGalaxies.pop.snd)
  termination_by n _ ci => (p.height - ci) + n
  worker [] ⟨0,p.not_empty.right⟩ (BinaryHeap.ofList sortGalaxiesByRow_wellDefinedLE galaxies)

/-- Output is from highest to lowest index! -/
def verticalVoids (galaxies : List (PixelPos p)) : List (Fin p.width) :=
    let rec worker : {n : Nat} → List (Fin p.width) → Fin p.width → BinaryHeap (PixelPos p) sortGalaxiesByColumn n → List (Fin p.width) := λ {n : Nat} previous currentIndex remainingGalaxies ↦
    match n with
    | 0 => previous
    | _+1 =>
      let next := remainingGalaxies.tree.root'
      if h : currentIndex < next.x then
        have : currentIndex + 1 < p.width := Nat.lt_of_le_of_lt (Nat.succ_le.mpr h) next.x.isLt
        worker (currentIndex :: previous) ⟨currentIndex + 1,this⟩ remainingGalaxies
      else if h₂ : currentIndex = next.x ∧ currentIndex + 1 < p.width then
        worker previous ⟨currentIndex+1, h₂.right⟩ (remainingGalaxies.pop.snd)
      else
        worker previous currentIndex (remainingGalaxies.pop.snd)
  termination_by n _ ci => (p.width - ci) + n
  worker [] ⟨0,p.not_empty.left⟩ (BinaryHeap.ofList sortGalaxiesByColumn_wellDefinedLE galaxies)

-- could use Fin here, but why?
structure ExpandedUniverseGalaxyCoordinate where
  x : Nat
  y : Nat
deriving Repr

def ExpandedUniverseGalaxyCoordinate.dist (a b : ExpandedUniverseGalaxyCoordinate) : Nat :=
  let dx := if a.x > b.x then a.x-b.x else b.x-a.x
  let dy := if a.y > b.y then a.y-b.y else b.y-a.y
  dx+dy

def expand (expansion : Nat) (galaxies : List (PixelPos p)) : List ExpandedUniverseGalaxyCoordinate :=
  let vVoids := verticalVoids galaxies
  let hVoids := horizontalVoids galaxies
  let horizontallyExpanded := galaxies.map λg ↦ vVoids.foldl (λc v ↦ if v.val ≤ c.x then {c with x := c.x+expansion} else c) (ExpandedUniverseGalaxyCoordinate.mk g.x g.y)
  horizontallyExpanded.map λg ↦ hVoids.foldl (λc h ↦ if h.val ≤ c.y then {c with y := c.y+expansion} else c) g

def part (expansion : Nat) (p : TelescopePicture) : Nat :=
  let g := galaxies p
  let e := expand expansion g
  let rec distances := λ d cs ↦
    match cs with
    | [] => d
    | c :: cs =>
      let d := cs.foldl (λa cc ↦ a + (cc.dist c)) d
      distances d cs
  distances 0 e

------------------------------------------------------------------------------------------

open DayPart
instance : Parse ⟨11, by simp⟩ (ι := TelescopePicture) where
  parse := Except.mapError toString ∘ (Parsing.RectangularGrid.ofString parseCharacter)

instance : Part ⟨11,_⟩ Parts.One (ι := TelescopePicture) (ρ := Nat) where
  run := some ∘ (part 1)

instance : Part ⟨11,_⟩ Parts.Two (ι := TelescopePicture) (ρ := Nat) where
  run := some ∘ (part (1000000 - 1))

------------------------------------------------------------------------------------------

private def testData := "
...#......
.......#..
#.........
..........
......#...
.#........
.........#
..........
.......#..
#...#.....
"

#eval
  let data := DayPart.Parse.parse ⟨11,_⟩ testData
  data.map (part (1000000 - 1))
