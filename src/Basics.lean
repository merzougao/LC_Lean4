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

def mergeCtx (c₁ c₂ : Ctx )  : Ctx := by
  cases c₁ 
  case nil => exact c₂ 
  case cons n t c₃ => exact n,,t ⟶ (mergeCtx c₃ c₂)
termination_by mergeCtx c₁ c₂ => ctxLength c₁ 
decreasing_by 
  simp_wf 
  cases c
  case nil => simp [ctxLength]
  case cons n₂ t₂ c₂ _ => 
    have h : (ctxLength (n,,t ⟶ n₂ ,, t₂ ⟶ c₂)) = (ctxLength (n₂,,t₂ ⟶ c₂ ) + 1) := by rfl
    rw [h]
    rw [Nat.add_one]
    apply Nat.lt_succ_of_le
    simp
    
    
    
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
  | var (n : Nat) (t : Typ) : Deduction (n,,t ⟶ []) (Term.var n t) t
  | abs {c : Ctx} {t : Term} {ty xt : Typ} {n : Nat} (d : Deduction (n,,xt ⟶ c) t ty) : Deduction c (Term.abs n xt t) (Typ.arrow xt ty)
  | app (c₁ c₂ : Ctx) ( t₁ t₂ : Term) (A B : Typ) (d₁ : Deduction c₁ t₁ (Typ.arrow A B)) (d₂ : Deduction c₂ t₂ A) : Deduction (mergeCtx c₁ c₂) (Term.app t₁ t₂) B
  | subst (c₁ c₂ : Ctx) (n₁ : Nat) (ty₁ ty : Typ) (t t₂ : Term) (d₁ : Deduction (n₁,,ty₁ ⟶ c₁) t ty) (d₂ : Deduction c₂ t₂ ty₁) : Deduction (mergeCtx c₁ c₂) (t [n₁ // t₂]) ty

notation Γ " ⊢ " t " : " ty => Deduction Γ t ty

theorem ProofId : (0,,base ⟶ []) ⊢ ($0:base) : base := Deduction.var 0 base

inductive red : Term → Term → Type
  | β (n: Nat) (ty : Typ) (t u : Term) : red ((λ (xn:ty).t)@u) (t[n // u])

-- Beta reduction preserves types --
theorem βTypePreservation {Γ₁ : Ctx} {tt : Typ} {t₁ t₂ : Term} 
                          (b : red t₁ t₂ ) (d₁ : Γ₁ ⊢ t₁ :tt) : (Γ₁ ⊢ t₂ : tt) := by
  cases b 
  case β n ty t₃ u => 
    let Γ : Ctx := mergeCtx Γ₁ Γ₁ 
    have : Γ₁ = mergeCtx Γ₁ Γ₁ := sorry
    rw [this]
    have d₃ : (n,,ty ⟶ Γ₁) ⊢ t₃ : tt := by
      sorry
    have d₄ : Γ₁ ⊢ u : ty := by
      sorry
    apply Deduction.subst Γ₁ Γ₁ n ty tt 
    case d₁ => exact d₃
    case d₂ => exact d₄ 
end Term
end Ctx
end Typ
