namespace String

def splitTrim (c : Char → Bool) (s : String) : List String :=
  String.trim <$> s.split c

def notEmpty : String → Bool := not ∘ isEmpty
