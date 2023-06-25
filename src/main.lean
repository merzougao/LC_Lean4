
notation "⊥" => Empty

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
| cons : Nat → Typ → Ctx → Ctx 

notation "[]" => Ctx.nil
notation n":"t"⊹"Γ => Ctx.cons n t Γ 

namespace Ctx 
#check []
#check 4:base ⊹ []
#check 4:base ⊹ 3:base ⊹ []

inductive inCtx : Nat → Ctx → Type 
| init : inCtx n (n:A ⊹ Γ) 
| cons : inCtx n Γ → inCtx n (n₁:A ⊹ Γ)

notation n"ε"Γ => inCtx n Γ
notation n"¬ε"Γ => inCtx n Γ → False

-- Return a proof that Γ₃ is Γ₁ ++ Γ₂ with no duplicates --
inductive mergeCtx : Ctx → Ctx → Ctx → Type
| nil_nil : mergeCtx [] [] []
| nil_cons : mergeCtx [] Γ Γ 
| cons_in (n : Nat) (Γ₁ Γ₂ Γ₃ : Ctx) : (n ε Γ₂) → mergeCtx Γ₁ Γ₂ Γ₃ → mergeCtx (n:A ⊹ Γ₁) Γ₂ Γ₃ 
| cons_out (n : Nat) (Γ₁ Γ₂ Γ₃ : Ctx) : (n ¬ε Γ₂) → mergeCtx Γ₁ Γ₂ Γ₃ → mergeCtx (n:A ⊹ Γ₁) Γ₂ (n:A ⊹ Γ₃) 

inductive validCtx : Ctx → Type 
| nil : validCtx []
| cons (n : Nat) (A : Typ) (Γ : Ctx) : (n ¬ε Γ) → validCtx Γ → validCtx (n:A ⊹ Γ)
notation Γ₃ " ≕ " Γ₁" ⊹ "Γ₂  => mergeCtx Γ₁ Γ₂ Γ₃ 

#check []≕[]⊹[]

inductive Term : Type
| var : Nat → Term
| abs : Nat → Term → Term 
| app : Term → Term → Term

notation "$"n  => Term.var n
notation "λ("n")."t => Term.abs n t
notation "("t₁")("t₂")" => Term.app t₁ t₂ 

namespace Term
#check $5 
#check λ(4).$5
#check (λ(4).$5)($7)

inductive Deduction : Ctx → Term → Typ → Type 
| var (n : Nat) (A : Typ) : Deduction (n:A ⊹ []) ($ n) A
| weak (n : Nat) (Γ : Ctx) (A : Typ) : (n ¬ε Γ) → Deduction Γ t A → Deduction (n:B ⊹ Γ) t A 
| comm (Γ : Ctx) (n₁ n₂ : Nat) (A₁ A₂ : Typ) (t : Term) :
      Deduction (n₁:A₁ ⊹ n₂:A₂ ⊹ Γ) t A →
      Deduction (n₂:A₂ ⊹ n₁:A₁ ⊹ Γ) t A
| abs (n: Nat) (Γ : Ctx) (A B : Typ) : Deduction (n:A ⊹ Γ) ($ n) A → Deduction Γ t B →  Deduction Γ (λ(n).t) (A->B)
| app (n : Nat) (Γ : Ctx) (t₁ t₂ : Term): Deduction Γ t₁ (A->B) → Deduction Γ t₂ A → Deduction Γ ((t₁)(t₂)) B

-- WARNING, This is "\:" not just ":" --
notation Γ " ⊢ " t " ∶ " A => Deduction Γ t A 
namespace Deduction

theorem ctxSoundness : (Γ ⊢ t ∶ A) → validCtx Γ := by 
  sorry
theorem ctxNotNilInDeduction {t : Term} {A : Typ} : ([] ⊢ t ∶ A) → False := by 
  sorry

theorem noDuplicatesInCtx {n : Nat} {A : Typ} {Γ : Ctx} : validCtx (n:A ⊹ Γ) → n ¬ε Γ := by sorry 

theorem invAbs {n : Nat} {Γ : Ctx} {A B : Typ} {t : Term}: (Γ ⊢ λ(x).t ∶ A->B) → (Γ ⊢ $ x ∶ A) := by 
  intro h 
  induction Γ 
  case nil => 
    have : False := by exact ctxNotNilInDeduction h  
    contradiction
  case cons n A₁ Γ₁ iH => 
    have : (Γ₁) ⊢ λ(x).t ∶ A->B := by sorry
    apply Deduction.weak 
    . intro d 
      have this2 : validCtx (n:A₁ ⊹ Γ₁) := ctxSoundness h 
      have this3 : n ¬ε Γ₁  := noDuplicatesInCtx this2 
      apply this3 
      exact d



theorem uniqVar {n n' : Nat} {A : Typ} : ((n:A ⊹ []) ⊢ ($ n') ∶ A) → n = n' := by 
  intro d  
  cases d 
  case var => rfl
  case weak h d₁ => contradiction 
    

theorem uniqVarInCtx {n n' : Nat} {Γ : Ctx} {t : Term} {A A' B : Typ} : ((n:A ⊹ n':A' ⊹ Γ) ⊢ t ∶ B) → n ≠ n' := by 
  intro h 
  induction t 
  case var n₁ => 
    cases h 
    case weak h' h'' => 
      intro h₁ 
      apply h'
      rw [h₁]
      apply inCtx.init
    case comm h' => 
      intro h₁ 
      have : validCtx (n':A' ⊹ n:A ⊹ Γ ) := by exact ctxSoundness h' 
      rw [h₁] at this 
      cases this 
      case cons hh hhh=> 
        apply hhh 
        apply inCtx.init 
  case abs n'' t' hh => 
    apply hh 
    

  case app => sorry



example (n₁ n₂ n₃ n₄ : Nat) (A₁ A₂ A₃ A₄ B: Typ) (t : Term) : 
  ((n₁:A₁  ⊹ n₂:A₂ ⊹ n₃:A₃  ⊹ n₄:A₄  ⊹ []) ⊢ t ∶ B) 
  → (n₁:A₁  ⊹ n₃:A₃  ⊹ n₂:A₂  ⊹ n₄:A₄  ⊹ []) ⊢ t ∶ B := by 
  intro d
  cases t 
  case var n' => 
    apply Deduction.weak 
    case a => 
      intro d₁ 
      sorry 
    case a => sorry
  case abs => sorry
  case app => sorry


theorem uniqTypForVar (n : Nat) (A B : Typ ) : ((n:A ⊹ []) ⊢ ($ n) ∶ B)→ A = B := by 
  intros d₂
  cases d₂ 
  case var => rfl
  case weak h d₁ => contradiction
  
variable (A B : Typ)
#check Deduction.var 0 (A->B->A)

--Any term can be constructed no matter the type if we allow free context --
example {A B : Typ} : Σ Γ : Ctx , Σ t : Term , (Γ ⊢ t ∶ A->B->A) := by
  let Γ := (0:A->B->A ⊹ [])
  let t := $0
  have p : Γ ⊢ t ∶ A->B->A := Deduction.var 0 (A->B->A)
  exact ⟨ Γ , ⟨ t , p⟩ ⟩ 

-- The story change if we only allow a restricted context, here we need a more intense derivation --

#check 0:base->base ⊹ 1:base ⊹ []

example {A B : Typ} : Σ t : Term , ((0:A->B ⊹ 1:A ⊹ []) ⊢ t ∶ A->B->A) := by
  constructor
  case fst => exact λ(1).($0)($1)
  case snd => 
    apply Deduction.abs
    . apply Deduction.weak 
      






