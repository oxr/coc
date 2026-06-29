inductive Lam : Type where
  | var : Nat → Lam
  | app : Lam → Lam → Lam
  | lam : Lam → Lam



inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons {n} : α → Vec α n → Vec α (n + 1)

inductive Finn : Nat → Type where
  | fzero {n} : Finn (n + 1)
  | finsucc {n} : Finn n → Finn (n + 1)


def Vec.proj : Vec α n → Finn n → α
  | cons x _  , Finn.fzero   => x
  | cons _ xs , Finn.finsucc i => xs.proj i

infixl:70 " !! " => Vec.proj


inductive ScLam : (n: Nat) → Type where
  | var {n} : Finn n → ScLam n
  | app {n} : ScLam n → ScLam n → ScLam n
  | lam {n} : ScLam (n + 1) → ScLam n

mutual
  -- neutral lambda terms -- are stuck, the head is a variable, and cannot be reduced further
  inductive NeLam : (n: Nat) → Type where
  | var {n} : Finn n → NeLam n
  | app {n} : NeLam n → NfLam n → NeLam n

  -- normal form lambda terms -- lambdas are fully reduced, and the head is a lambda abstraction
  inductive NfLam : (n: Nat) → Type where
  | lam {n} : NfLam (n + 1) → NfLam n
  | ne {n} : NeLam n → NfLam n

end


-----------------

inductive W (α : Type) (β : α → Type) : Type where
  | sup : (a : α) → (f : β a → W α β) → W α β


def wrec {α : Type}{β : α → Type}(C : W α β → Type)
  (h : (a : α) → (f : β a → W α β) → ((x : β a) → C (f x)) → C (W.sup a f))
  : (t : W α β) → C t
  | W.sup a f => h a f (fun x => wrec C h (f x))


inductive IdType {A : Type}(x : A) : {B : Type} → B → Type where
  | refl : IdType x x



def subst {A : Type}(P : A → Type){x : A}{y : A}
  : IdType x y → P x → P y
  | .refl , x => x

infixl:75 " ≅ " => IdType

#check 3 ≅ 4

def equiv {A : Type} : A → A → Type := fun x y => x ≅ y

infixl:75 " ≡ " => equiv

structure Cont : Type 1 where
  (α : Type)
  (β : α → Type)

infixl:75 " ▹ " => Cont.mk
#check (Nat ▹ fun _ => Bool)


def contExt (c : Cont) (X : Type) : Type :=
  Σ a : c.α, c.β a → X

notation "⟦" c "⟧" => contExt c

instance (c : Cont) : Functor (contExt c) where
  map f := fun ⟨a, g⟩ => ⟨a, f ∘ g⟩

structure ContHom (c d : Cont) : Type 1 where
  shapeMap : c.α → d.α
  posMap   : (a : c.α) → d.β (shapeMap a) → c.β a

infixr:25 " ⇒ " => ContHom

def ContHom.natTrans {c d : Cont} (m : c ⇒ d) (X : Type) : ⟦ c ⟧ X → ⟦ d ⟧ X :=
  fun ⟨a, g⟩ => ⟨m.shapeMap a, g ∘ m.posMap a⟩

-- 1-position container: shape Unit, one position
def Cont1 : Cont := Unit ▹ fun _ => Unit

-- 2-position container: shape Unit, two positions
def Cont2 : Cont := Unit ▹ fun _ => Bool

-- morphism Cont1 ⇒ Cont2: duplicate the single element into both positions
def dup : Cont1 ⇒ Cont2 :=
  { shapeMap := fun () => ()
    posMap   := fun () _ => () }

-- container of vectors of length n
def ContVec (α : Type) : Cont :=
  Nat ▹ fun n => Vec α n
