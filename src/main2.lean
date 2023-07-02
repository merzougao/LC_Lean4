
inductive Typ : Type 
  | base : Typ
  | arrow : Typ → Typ → Typ

notation A" -> "B => Typ.arrow A B 

namespace Typ

inductive Var : Type 
  | consf : Nat → Typ → Var
  | consb : Nat → Typ → Var

notation x":f:"A => Var.consf x A
notation x":b:"A => Var.consb x A

inductive Term : Type 
  | var : Nat → Term
  | abs : Nat → Term → Term 
  | app : Term → Term → Term 
  | subst : Nat → Term → Term → Term 

notation  "$"x => Term.var x
notation "λ("x")."t => Term.abs x t
notation t"("t'")" => Term.app t t'
notation t"["x"//"u"]" => Term.subst x u t

namespace Term 

inductive Ctx : Type 
  | nil : Ctx
  | cons : Var → Ctx → Ctx 

notation "[]" => Ctx.nil
notation x" , "Γ => Ctx.cons x Γ

inductive notInCtx : Nat → Ctx → Type 
  | nil : notInCtx n []
  | cons : n ≠ x → notInCtx n Γ → notInCtx n ((x:f:A) , Γ)

inductive validCtx : Ctx → Type 
  | nil : validCtx []
  | consf : notInCtx x Γ → validCtx Γ → validCtx ((x:f:A) , Γ)
  | consb : validCtx Γ → validCtx ((x:b:A) , Γ)

inductive Deduction : Ctx → Term → Typ → Type 
  | var : Deduction ((x:f:A) , []) ($ x) A
  | abs : Deduction ((x:f:A) , Γ ) t B → Deduction ((x:b:A) , Γ ) (λ(x).t) (A->B)
  | app : Deduction Γ t (A->B) → Deduction Γ t' A → Deduction Γ (t(t')) B
  | weak : validCtx ((x:f:A) , Γ) → Deduction Γ t B → Deduction ((x:f:A), Γ) t B
  | subst : Deduction ((x:f:A) , Γ) t B → Deduction Γ u A → Deduction Γ (t[x//u]) B
  
  
notation Γ " ⊢ " t " : " A => Deduction Γ t A 

theorem ctxSoundness : (Γ ⊢ t : A) → validCtx Γ := by 
  intro d
  induction d 
  case var x B => 
    apply validCtx.consf 
    . apply notInCtx.nil 
    . apply validCtx.init
  case abs  => assumption
  case app  => assumption
  case weak  => assumption 
  case subst => assumption 


inductive βreduction : Term → Term → Type 
  | cons : βreduction ((λ(x).t)(u)) (t[x//u])

notation t₁ " ▸β " t₂ => βreduction t₁ t₂ 

example {A B : Typ} : Σ (t : Term) , ((1:b:A) , (0:f:B->A) , []) ⊢ t : A->B->A := by
  constructor 
  case fst => exact λ(1).$0
  case snd => 
    apply Deduction.abs 
    apply Deduction.weak 
    . apply validCtx.consf 
      . apply notInCtx.cons 
        . trivial
        . apply notInCtx.nil 
      . apply validCtx.consf 
        . apply notInCtx.nil
        . apply validCtx.nil
    . apply Deduction.var 

      
theorem reductionsPreserveTypes :  (t₁ ▸β t₂) → (Γ ⊢ t₁ : A) → (Γ ⊢ t₂ : A) := by 
  intro d₁ d₂ 
  induction d₂ 
  case var  x B => contradiction
  case abs => contradiction
  case app => sorry
  case weak =>sorry 
  case subst => contradiction

