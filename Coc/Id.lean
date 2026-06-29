inductive IdType {A : Type}(x : A) : {B : Type} → B → Type where
  | refl : IdType x x



def subst {A : Type}(P : A → Type){x : A}{y : A}
  : IdType x y → P x → P y
  | .refl , x => x

infixl:75 " ≅ " => IdType

#check 3 ≅ 4

def equiv {A : Type} : A → A → Type := fun x y => x ≅ y

infixl:75 " ≡ " => equiv
