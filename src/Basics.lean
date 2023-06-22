import Init.Data.Nat.Basic 

--theorem natPos (n : Nat) (p : n ≠ 0) : n > 0 := by 
--  cases n
--  case zero => contradiction
--  case succ n₂ => exact Nat.succ_add 


-- We start by defining our basic type base and the arrow type --
inductive Typ : Type
  | base : Typ
  | arrow : Typ → Typ → Typ

notation t₁ "->" t₂ => Typ.arrow t₁ t₂ 

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
notation n ",," t " ⟶ " c => Ctx.cons n t c

-- A type that is inhabited whenever a variable is not present in a context --
inductive notInCtx (n : Nat) (t : Typ) : Ctx → Type 
  | nil : notInCtx n t []
  | cons (n₁ : Nat) (t₁ : Typ) (p₁ : Ctx) (p : n ≠ n₁) : notInCtx n t (n₁,,t₁ ⟶ p₁)

-- A type that is inhabited whenever a context is valid, i.e does not contain duplicates --
inductive validCtx : Ctx → Type
  | nil : validCtx []
  | cons (n : Nat) (t : Typ) (c : Ctx) (p : notInCtx n t c) : validCtx (n,,t ⟶ c)

namespace Ctx

def ctxLength (c : Ctx) : Nat := by
  cases c
  case nil => exact 0
  case cons n t c₁ => exact ctxLength c₁ + 1

inductive mergeCtx : Ctx → Ctx → Ctx → Type 
  | nil_nil : mergeCtx [] [] []
  | nill (c : Ctx) : mergeCtx [] c c
  | nilr (c : Ctx) : mergeCtx c [] c
  | consl  (c₁ c₂ c₃ : Ctx) 
          (n  : Nat) 
          (t : Typ) :
          (mergeCtx c₁ c₂ c₃)
          → (notInCtx n t c₂) 
          → mergeCtx (n,,t  ⟶ c₁) c₂ (n ,,t  ⟶ c₃ )
  | consr  (c₁ c₂ c₃ : Ctx) 
          (n  : Nat) 
          (t : Typ) :
          (mergeCtx c₁ c₂ c₃)
          → (notInCtx n t c₁) 
          → mergeCtx c₁ (n,,t  ⟶ c₂ ) (n ,,t ⟶ c₃ )

    
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
  | abs : Nat → Typ →  Term → Term
  | app : Term → Term → Term

notation "λ (x"n":"t")."te => Term.abs n t te
notation "$"n":"t => Term.var n t
notation f"@"t => Term.app f t

def printTerm (t: Term) : String := by
  cases t
  case var n t₁ => exact "x"++(toString n)
  case abs  n ty t₁ => exact "λ (x" ++ toString n ++ ":" ++ (printTyp ty) ++")."++ printTerm t₁ 
  case app t₁ t₂ => exact "("++ printTerm t₁ ++ ")("++ printTerm t₂ ++ ")"

namespace Term

def substitute (n : Nat) (t u : Term) : Term := by
  cases t
  case var n₁ t₁ => exact u
  case abs n₁ ty t₁ => exact if n = n₁ then Term.abs n₁ ty t₁  else Term.abs n₁ ty (substitute n t₁ u)
  case app t₁ t₂ => exact Term.app (substitute n t₁ u) (substitute n t₁ u)

notation t "[" x "//" u "]" => substitute x t u

def t : Term := Term.var 0 base
def u : Term := Term.var 1 base
def t₁ : Term := Term.abs 0 base (Term.var 0 base)

#eval printTerm t
#eval printTerm u
#eval printTerm (t [0//u])
#eval printTerm t₁ 
#eval printTerm (t₁ [0//u])

inductive Deduction : Ctx →  Term →  Typ →  Type
  | var (n : Nat) (t : Typ) : Deduction (n,,t ⟶ []) ($n:t) t
  | weak (n : Nat) (A B : Typ) (t : Term) (Γ : Ctx) : Deduction (n,,A ⟶ Γ) t B 
  | comm (Γ c₁ c₂ c : Ctx) (bn₁ bn₂ A : Typ) :
        mergeCtx Γ (n₁,,Bn₁ ⟶ n₂,,Bn₂ ⟶ c) c₁ 
      → Deduction c₁ t A
      → mergeCtx Γ (n₂,,Bn₂ ⟶ n₁,,Bn₁ ⟶ c) c₂
      → Deduction c₂ t A
  | abs (c : Ctx) (t : Term) (ty xt : Typ) (n : Nat) : 
        Deduction (n,,xt ⟶ c) t ty 
      → Deduction c (λ (xn:xt).t) (xt -> ty)
  | app (c₁ c₂ c₃ : Ctx) ( t₁ t₂ : Term) (A B : Typ) : 
        Deduction c₁ t₁ (A -> B) 
      → Deduction c₂ t₂ A 
      → mergeCtx c₁ c₂ c₃
      → Deduction c₃ (t₁ @ t₂) B
--  | subst (c₁ c₂ c₃ : Ctx) (n₁ : Nat) (ty₁ ty : Typ) (t t₂ : Term) :
--        Deduction (n₁,,ty₁ ⟶ c₁) t ty 
--      → Deduction c₂ t₂ ty₁
--      → mergeCtx c₁ c₂ c₃  
--      → Deduction c₃ (t [n₁ // t₂]) ty
--
notation Γ " ⊢ " t " : " ty => Deduction Γ t ty

theorem ProofId : (0,,base ⟶ []) ⊢ ($0:base) : base := Deduction.var [] 0 base

inductive red : Term → Term → Type
  | β (n: Nat) (ty : Typ) (t u : Term) : red ((λ (xn:ty).t)@u) (t[n // u])

theorem arrowNotEq (A B : Typ) : (A -> B) ≠ A := by
  intros h 
  induction A 
  case base => 
    induction B 
    case base => trivial
    case arrow B₁ B₂ h p =>  
  

theorem typeApp {Γ : Ctx} {t₁ t₂ : Term} {A B : Typ} : (Γ ⊢ t₁ : A -> B) → (Γ ⊢ t₁ @ t₂ : B) → (Γ ⊢ t₂ : A) := by
  intros d₁ d₂ 
  cases d₁ 
  case var n => 
    induction t₂
    case var n₁ C =>  
      have : C = A := by sorry
      rw [this]
      have : n = n₁ := by sorry
      rw [this]
      have : (A -> B) = A := by sorry
      


    case abs h p q => sorry
    case app h p => sorry

  case weak => sorry
  case comm => sorry
  case abs => sorry
  case app => sorry


--theorem βRedPreservesType (Γ : Ctx) (A : Typ) (t₁ t₂ : Term) : red t₁ t₂ → (Γ ⊢ t₁ : A) → (Γ ⊢ t₂ : A ):= by 
--  intros r d₁ 
--  induction t₁ 
--  case var n An => contradiction
--  case abs n An t₃ h => contradiction
--  case app t₃ t₄ h p => 
--    induction t₃ 
--    case var => contradiction
--    case abs n₁ an₁ t₅ h₁ => 
--      apply p 
--      . 
--      
--    case app => contradiction
end Term
end Ctx
end Typ
