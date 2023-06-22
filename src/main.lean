
inductive Typ : Type
| base : Typ
| arrow : Typ → Typ → Typ

notation A"->"B => Typ.arrow A B

namespace Typ 
#check base 
#check base->base 
#check base->base->base 

example (A B : Typ ) : (A->B) ≠ A := by 
  intro h
  induction A 
  case base => contradiction
  case arrow A₁ B₁ Ah _ =>
    injection h with h₁ h₂  
    apply Ah 
    rw [← h₂] at h₁ 
    assumption

inductive Ctx : Type
| nil : Ctx 
| cons : Nat → Ctx → Ctx 

notation "[]" => Ctx.nil
notation n"⊹"Γ => Ctx.cons n Γ 

namespace Ctx 
#check []
#check 4 ⊹ []
#check 4 ⊹ 3 ⊹ []

inductive notInCtx : Nat → Ctx → Type 
| nil : notInCtx n []
| cons : n₁ ≠ n₂ → notInCtx n₁ Γ → notInCtx n₁ (n₂ ⊹ Γ)   

notation n"¬ε"Γ => notInCtx n Γ

inductive Term : Type
| var : Nat → Term
| abs : Nat → Term → Term 
| app : Term → Term → Term

notation "$"n  => Term.var n
notation n"↦"t => Term.abs n t
notation t₁"@"t₂ => Term.app t₁ t₂ 

namespace Term
#check $5 
#check 4 ↦ $5
#check (4 ↦ $5)@$7

inductive Deduction : Ctx → Term → Typ → Type 
| var : Deduction (n ⊹ []) ($ n) A
--| weak : (n ¬ε Γ) → Deduction Γ t A → Deduction (n ⊹ Γ) t A 
| abs : Deduction (n ⊹ Γ) ($ n) A → Deduction Γ t B →  Deduction Γ (n ↦ t) (A->B)

notation Γ "⊢" t ":" A => Deduction Γ t A 
namespace Deduction












