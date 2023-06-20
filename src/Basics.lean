-- We start by defining our basic type base and the arrow type --
inductive Typ : Type
  | base : Typ
  | arrow : Typ → Typ → Typ

-- Print function for convenience --
def printTyp (t : Typ) : String := by 
  cases t 
  case base => exact " base " 
  case arrow t₁ t₂ => exact printTyp t₁ ++ "→" ++ printTyp t₂ 

namespace Typ

-- We define a context, which is just a list of variable and types --
inductive Ctx : Type
  | nil   : Ctx
  | cons  (n : Nat)  (t : Typ) (c : Ctx ) : Ctx 

notation "[]" => Ctx.nil
notation n "," t " ⟶ " c => Ctx.cons n t c
notation "("n",,"t")" => n,t ⟶ []

-- A type that is inhabited whenever a variable is not present in a context --
inductive notInCtx (n : Nat) (t : Typ) : Ctx → Type 
  | nil : notInCtx n t []
  | cons (n₁ : Nat) (t₁ : Typ) (p₁ : Ctx) (p : n ≠ n₁) : notInCtx n t (n₁,t₁ ⟶ p₁)

-- A type that is inhabited whenever a context is valid, i.e does not contain duplicates --
inductive validCtx : Ctx → Type
  | nil : validCtx []
  | cons (n : Nat) (t : Typ) (c : Ctx) (p : notInCtx n t c) : validCtx (n,t ⟶ c)

namespace Ctx

def ctxLength (c : Ctx) : Nat := by
  cases c
  case nil => exact 0
  case cons n t c₁ => exact ctxLength c₁ + 1

def printCtx (c : Ctx) : String := by
  cases c
  case nil => exact ""
  case cons n t c  => exact "(" ++ toString n ++ printTyp t ++ ")" ++ printCtx c

-- Let's define a context and prove that it is a valid one --
-- Note that if we define an invalid context, there will be no proof of it being valid --
def ctx₁ : Ctx := cons 2 base (cons 3 (arrow base base) nil)
#check ctx₁ 
#eval printCtx ctx₁ 

-- A Proof that the previous context is a valid context --
example : validCtx ctx₁ := by
  apply validCtx.cons 
  apply notInCtx.cons 
  trivial

inductive Term : Type
  | var : Nat → Typ → Term
  | abs (t : Typ ) : Term → Term
  | app : Term → Term → Term

namespace Term

def mergeCtx : Ctx → Ctx → Ctx := sorry

inductive Deduction : Ctx →  Term →  Typ →  Type
  | var (n : Nat) (t : Typ) : Deduction (n,,t) (Term.var n t) t
  | abs {c : Ctx} {t : Term} {ty xt : Typ} {n : Nat} (d : Deduction (n,xt ⟶ c) t ty) : Deduction c (Term.abs xt t) (Typ.arrow xt ty)
  | app {c₁ c₂ : Ctx} { t₁ t₂ : Term} {A B : Typ} (d₁ : Deduction c₁ t₁ (Typ.arrow A B)) (d₂ : Deduction c₂ t₂ A) : Deduction (mergeCtx c₁ c₂) (Term.app t₁ t₂) B
  
notation Γ " ⊢ " t " : " ty => Deduction Γ t ty

theorem ProofId : (0,,base) ⊢ (Term.var 0 base) : base := Deduction.var 0 base
  
  

end Term
end Ctx
end Typ
