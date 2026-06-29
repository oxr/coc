-- A polynomial functor arises from a morphism f : A → B
-- B is the base (shapes), A is the total space (positions)
structure Poly where
  B   : Type
  A   : Type
  arr : A → B

-- fiber of arr over b : the positions at shape b
def Poly.fiber (p : Poly) (b : p.B) : Type :=
  Σ a : p.A, p.arr a = b

-- extension of a polynomial to a functor
def Poly.ext (p : Poly) (X : Type) : Type :=
  Σ b : p.B, p.fiber b → X

-- morphism of polynomials: a map on bases and a fiberwise map going backwards
structure PolyHom (p q : Poly) where
  baseMap  : p.B → q.B
  fiberMap : (b : p.B) → q.fiber (baseMap b) → p.fiber b

infixr:25 " ⟹ " => PolyHom

-- the natural transformation induced by a polynomial morphism
def PolyHom.natTrans {p q : Poly} (m : p ⟹ q) (X : Type) : p.ext X → q.ext X :=
  fun ⟨b, g⟩ => ⟨m.baseMap b, g ∘ m.fiberMap b⟩
