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


/--
  SORTED FROM LARGEST TO SMALLEST VOID! That's what is easiest to use during expansion.
  Also, does not include voids after the last galaxy.
 -/
def horizontalVoids (galaxies : List (PixelPos p)) : List (Fin p.height) :=
  let rec worker : {n : Nat} → Fin p.height → BinaryHeap (PixelPos p) sortGalaxiesByRow n → List (Fin p.height) := λ {n : Nat} currentIndex remainingGalaxies ↦
    match n with
    | 0 => []
    | _+1 =>
      let next := remainingGalaxies.tree.root'
      if h : currentIndex < next.y then
        have : currentIndex + 1 < p.height := Nat.lt_of_le_of_lt (Nat.succ_le.mpr h) next.y.isLt
        currentIndex :: worker ⟨currentIndex + 1,this⟩ remainingGalaxies
      else if h₂ : currentIndex = next.y ∧ currentIndex + 1 < p.height then
        worker ⟨currentIndex+1, h₂.right⟩ (remainingGalaxies.pop.snd)
      else
        worker currentIndex (remainingGalaxies.pop.snd)
  termination_by n ci => (p.height - ci) + n
  worker ⟨0,p.not_empty.right⟩ (BinaryHeap.ofList sortGalaxiesByRow_wellDefinedLE galaxies)

------------------------------------------------------------------------------------------

open DayPart
instance : Parse ⟨11, by simp⟩ (ι := TelescopePicture) where
  parse := Except.mapError toString ∘ (Parsing.RectangularGrid.ofString parseCharacter)

------------------------------------------------------------------------------------------

private def testData := "...#......
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
  match data with
  | .error _ => none
  | .ok picture =>
    let gs := galaxies picture
    let gs := horizontalVoids gs
    let gs := gs.map Fin.val
    some gs
