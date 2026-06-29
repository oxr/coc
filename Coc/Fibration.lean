import Coc.Id
--
def toFamily {A B : Type} : (A → B) -> B → Type :=
  fun f b => Σ (a : A) , f a ≡ b

def toFibration {A : Type} (f : A → Type) : (Σ a : A , f a) → A := Sigma.fst
