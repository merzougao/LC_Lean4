
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
| init (Γ : Ctx) (n : Nat) (A : Typ) : inCtx n (n:A ⊹ Γ) 
| cons (Γ : Ctx) (n n₁ : Nat) (A : Typ) : inCtx n Γ → inCtx n (n₁:A ⊹ Γ)

notation n"ε"Γ => inCtx n Γ
notation n"¬ε"Γ => inCtx n Γ → false

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


theorem invAbs {n : Nat} {Γ : Ctx} {A B : Typ} {t : Term}: (Γ ⊢ λ(x).t ∶ A->B) → (Γ ⊢ $ x ∶ A) := by 
    sorry

-- If a weakest context is valid, then a strongest one remains valid --
theorem weakValidCtx (Γ : Ctx) (n₁ : Nat) (A₁ : Typ) : validCtx (n₁:A₁ ⊹ Γ) → validCtx Γ  := by 
  intro d 
  cases d 
  case cons A₂ h₁ => assumption

-- Contexts remain valid if we commute their variables ( this should not provable in dependent type theory ! ) --
theorem commValidCtx {Γ : Ctx} {n₁ n₂ : Nat} {A₁ A₂ : Typ} : validCtx (n₁:A₁ ⊹ n₂:A₂ ⊹ Γ ) → validCtx (n₂:A₂ ⊹ n₁:A₁ ⊹ Γ ) := by
  intro d 
  apply validCtx.cons 
  . intro d₁ 
    cases d 
    case a h₁ h₂ => 
      apply h₂ 
      apply inCtx.cons 
      cases h₁ 
      case a.cons h₃ h₄ => 
        cases d₁ 
        case init => have that : false = true := h₂ (inCtx.init Γ n₁ A₂) ;contradiction
        case cons h₅ => have that : false = true := h₄ h₅ ; contradiction
  . apply validCtx.cons 
    intro d₁ 
    cases d 
    case a.a.cons h₁ h₂ => 
      apply h₂;apply inCtx.cons;assumption
    case a.a => exact weakValidCtx Γ n₂ A₂ (weakValidCtx (n₂:A₂ ⊹ Γ) n₁ A₁ d)
    
-- Prove the soundness of context when a judgment of the form Γ ⊢ x : A is made and x is avariable --
-- i.e, whenever the judgement is present, the context Γ has to be valid --
theorem ctxSoundnessVar {n : Nat} {Γ : Ctx} {A : Typ} {t : Term} : (t = $ n ) → (Γ ⊢ t ∶ A) → validCtx Γ := by 
  intro d₁ d₂ 
  induction d₂ 
  case var n₁ A₁ => 
    apply validCtx.cons
    intro d₃ 
    . contradiction
    . exact validCtx.nil
  case weak t₁ t₂ B n₁ _ A₁ _ h₂ =>
    apply validCtx.cons 
    . assumption 
    . exact h₂ d₁ 
  case comm A₁ Γ₁ n₁ n₂ B₁ B₂ t₁ h₂ h₃ => 
    apply validCtx.cons 
    . intro d₃ 
      cases h₃ d₁ 
      case a.cons h₄ h₅ => 
        apply h₅;cases d₃ 
        case init => exact inCtx.init 
        case cons h₆ => 
          cases h₄ 
          case cons h₇ h₈ => have : false = true := h₈ h₆;contradiction 
    . apply validCtx.cons 
      . intro d₃ 
        cases h₃ d₁ 
        case a.a.cons h₅ h₆ => apply h₆ ; apply inCtx.cons ; assumption 
      . cases h₃ d₁
        case a.a.cons h₅ h₆ => cases h₅ ; case cons h₇ h₈ => assumption 
  case abs t₁ n₁ Γ₁ _ _ _ _ _ _  => contradiction
  case app Γ₁ t₁ t₂ _ _ _ _ => contradiction
 
-- Prove the soundness of context when a judgment of the form Γ ⊢ t : A is made --
-- i.e, whenever the judgement is present, the context Γ has to be valid --
theorem ctxSoundness : (Γ ⊢ t ∶ A) → validCtx Γ := by 
  intro d 
  induction d 
  case var n A₁ => 
    apply validCtx.cons 
    . intro d₁;contradiction 
    . exact validCtx.nil
  case weak => apply validCtx.cons <;> assumption
  case comm h₃ => exact commValidCtx h₃
  case abs h₄ => exact h₄ 
  case app h₃ => exact h₃ 
    

theorem ctxNotNilInDeduction {t : Term} {A : Typ} : ([] ⊢ t ∶ A) → False := by 
  induction t
  case var n => 
    intro d 
    contradiction
  case abs n t₁ h => 
    intro d 
  case app => sorry

theorem noDuplicatesInCtx {n : Nat} {A : Typ} {Γ : Ctx} : validCtx (n:A ⊹ Γ) → n ¬ε Γ := by sorry 




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
      






