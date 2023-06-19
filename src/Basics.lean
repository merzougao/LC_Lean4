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

-- A type that is inhabited whenever a variable is not present in a context --
inductive notInCtx (n : Nat) (t : Typ) : Ctx → Type 
  | nil : notInCtx n t Ctx.nil
  | cons (n₁ : Nat) (t₁ : Typ) (p₁ : Ctx) (p : n ≠ n₁) : notInCtx n t (Ctx.cons n₁ t₁ p₁)

-- A type that is inhabited whenever a context is valid, i.e does not contain duplicates --
inductive validCtx : Ctx → Type
  | nil : validCtx nil
  | cons (n : Nat) (t : Typ) (c : Ctx) (p : notInCtx n t c) : validCtx (Ctx.cons n t c)

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
  | var : Typ → Term
  | abs : var → Term
  | app : Term → Term → Term

namespace Term

def freshVarIndex (c : Ctx) : Nat := by
  cases c
  case nil => exact 1
  case cons n t c₁ => exact freshVarIndex c₁ + 1
def mergeCtxs (c₁ c₂ : Ctx) : Ctx := by
  cases c₁
  case nil => exact c₂ 
  case cons n t c₃ => exact Ctx.cons n t (mergeCtxs c₃ c₂ )
termination_by mergeCtxs c₁ c₂ => ctxLength c₁
decreasing_by 
  sorry

def contextFromTerm (t : Term)  (c : Ctx ) :  Ctx := by
  cases t
  case var t₁ => exact Ctx.cons  (freshVarIndex c) t₁ Ctx.nil 
  case abs v tt => exact c
  case app t₁ t₂ => exact mergeCtxs (contextFromTerm t₁ Ctx.nil) (contextFromTerm t₂ Ctx.nil) 

--def ctxFromTerm (counter : Nat ) (t : Term) : Ctx := by
--  cases t
--  case var ty => exact Ctx.cons counter + 1 ty Ctx.nil
--  case abs v => exact 
--  case app t₁ t₂  => sorry
--

end Term
end Ctx
end Typ
