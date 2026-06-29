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
