import «Common»

namespace Day7

inductive Card
  | two
  | three
  | four
  | five
  | six
  | seven
  | eight
  | nine
  | ten
  | jack
  | queen
  | king
  | ace
  deriving Repr, Ord, BEq

inductive Hand
  | mk : Card → Card → Card → Card → Card → Hand
  deriving Repr, BEq

private inductive Score
  | highCard
  | onePair
  | twoPair
  | threeOfAKind
  | fullHouse
  | fourOfAKind
  | fiveOfAKind
  deriving Repr, Ord, BEq

-- we need countCards in part 2 again, but there it has different types
private class CardList (η : Type) (χ : outParam Type) where
  cardList : η → List χ

-- similarly, we can implement Ord in terms of CardList and Score
private class Scorable (η : Type) where
  score : η → Score

private instance : CardList Hand Card where
  cardList := λ
    | .mk a b c d e => [a,b,c,d,e]

private def countCards {η χ : Type} (input :η) [CardList η χ] [Ord χ] [BEq χ] : List (Nat × χ) :=
  let ordered := (CardList.cardList input).quicksort
  let helper := λ (a : List (Nat × χ)) (c : χ) ↦ match a with
  | [] => [(1, c)]
  | a :: as =>
    if a.snd == c then
      (a.fst + 1, c) :: as
    else
      (1, c) :: a :: as
  List.quicksortBy (·.fst > ·.fst) $ ordered.foldl helper []

private def evaluateCountedCards : (l : List (Nat × α)) → Score
  | [_] => Score.fiveOfAKind -- only one entry means all cards are equal
  | (4,_) :: _ => Score.fourOfAKind
  | [(3,_), (2,_)] => Score.fullHouse
  | (3,_) :: _ => Score.threeOfAKind
  | [(2,_), (2,_), _] => Score.twoPair
  | (2,_) :: _ => Score.onePair
  | _ => Score.highCard

private def Hand.score (hand : Hand) : Score :=
  evaluateCountedCards $ countCards hand

private instance : Scorable Hand where
  score := Hand.score

instance {σ χ : Type} [Scorable σ] [CardList σ χ] [Ord χ] : Ord σ where
  compare (a b : σ) :=
    let comparedScores := Ord.compare (Scorable.score a) (Scorable.score b)
    if comparedScores != Ordering.eq then
      comparedScores
    else
      Ord.compare (CardList.cardList a) (CardList.cardList b)

private def Card.fromChar? : Char → Option Card
| '2' => some Card.two
| '3' => some Card.three
| '4' => some Card.four
| '5' => some Card.five
| '6' => some Card.six
| '7' => some Card.seven
| '8' => some Card.eight
| '9' => some Card.nine
| 'T' => some Card.ten
| 'J' => some Card.jack
| 'Q' => some Card.queen
| 'K' => some Card.king
| 'A' => some Card.ace
| _ => none

private def Hand.fromString? (input : String) : Option Hand :=
  match input.toList.mapM Card.fromChar? with
  | some [a, b, c, d, e] => Hand.mk a b c d e
  | _ => none

abbrev Bet := Nat

structure Player where
  hand : Hand
  bet : Bet
  deriving Repr

def parse (input : String) : Except String (List Player) := do
  let lines := input.splitOn "\n" |> List.map String.trim |> List.filter String.notEmpty
  let parseLine := λ (line : String) ↦
    if let [hand, bid] := line.split Char.isWhitespace |> List.map String.trim |> List.filter String.notEmpty then
      Option.zip (Hand.fromString? hand) (String.toNat? bid)
      |> Option.map (uncurry Player.mk)
      |> Option.toExcept s!"Line could not be parsed: {line}"
    else
      throw s!"Failed to parse. Line did not separate into hand and bid properly: {line}"
  lines.mapM parseLine

def part1 (players : List Player) : Nat :=
  players.quicksortBy (λ p q ↦ p.hand < q.hand)
  |> List.enumFrom 1
  |> List.foldl (λ r p ↦ p.fst * p.snd.bet + r) 0


------------------------------------------------------------------------------------------------------
-- Again a riddle where part 2 needs different data representation, why are you doing this to me? Why?
-- (Though, strictly speaking, I could just add "joker" to the list of cards in part 1 and treat it special)

private inductive Card2
  | joker
  | two
  | three
  | four
  | five
  | six
  | seven
  | eight
  | nine
  | ten
  | queen
  | king
  | ace
  deriving Repr, Ord, BEq

private def Card.toCard2 : Card → Card2
  | .two => Card2.two
  | .three => Card2.three
  | .four => Card2.four
  | .five => Card2.five
  | .six => Card2.six
  | .seven => Card2.seven
  | .eight => Card2.eight
  | .nine => Card2.nine
  | .ten => Card2.ten
  | .jack => Card2.joker
  | .queen => Card2.queen
  | .king => Card2.king
  | .ace => Card2.ace

private inductive Hand2
  | mk : Card2 → Card2 → Card2 → Card2 → Card2 → Hand2
  deriving Repr

private def Hand.toHand2 : Hand → Hand2
  | Hand.mk a b c d e => Hand2.mk a.toCard2 b.toCard2 c.toCard2 d.toCard2 e.toCard2

instance : CardList Hand2 Card2 where
  cardList := λ
    | .mk a b c d e => [a,b,c,d,e]

private def Hand2.score (hand : Hand2) : Score :=
  -- I could be dumb here and just let jokers be any other card, but that would be really wasteful
  -- Also, I'm pretty sure there is no combination that would benefit from jokers being mapped to
  -- different cards.
  -- and, even more important, I think we can always map jokers to the most frequent card and are
  -- still correct.
  let counted := countCards hand
  let (jokers, others) := counted.partition λ e ↦ e.snd == Card2.joker
  let jokersReplaced := match jokers, others with
  | (jokers, _) :: _ , (a, ac) :: as => (a+jokers, ac) :: as
  | _ :: _, [] => jokers
  | [], others => others
  evaluateCountedCards jokersReplaced

private instance : Scorable Hand2 where
  score := Hand2.score

private structure Player2 where
  bet : Bet
  hand2 : Hand2

def part2 (players : List Player) : Nat :=
  let players := players.map λ p ↦
    {bet := p.bet, hand2 := p.hand.toHand2 : Player2}
  players.quicksortBy (λ p q ↦ p.hand2 < q.hand2)
  |> List.enumFrom 1
  |> List.foldl (λ r p ↦ p.fst * p.snd.bet + r) 0

----------------------------------------------------------------------------------------------------
open DayPart

instance : Parse ⟨7,by simp⟩ (ι := List Player) where
  parse := parse

instance : Part ⟨7,_⟩ Parts.One (ι := List Player) (ρ := Nat) where
  run := some ∘ part1

instance : Part ⟨7,_⟩ Parts.Two (ι := List Player) (ρ := Nat) where
  run := some ∘ part2
