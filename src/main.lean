
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
notation n":"t","Γ => Ctx.cons n t Γ 

namespace Ctx 
#check []
#check 4:base , []
#check 4:base , 3:base , []

inductive inCtx : Nat → Ctx → Type 
| init (Γ : Ctx) (n : Nat) (A : Typ) : inCtx n (n:A , Γ) 
| cons (Γ : Ctx) (n n₁ : Nat) (A : Typ) : inCtx n Γ → inCtx n (n₁:A , Γ)

notation n"ε"Γ => inCtx n Γ
notation n"¬ε"Γ => inCtx n Γ → false

inductive validCtx : Ctx → Type 
| nil : validCtx []
| cons (n : Nat) (A : Typ) (Γ : Ctx) : (n ¬ε Γ) → validCtx Γ → validCtx (n:A , Γ) 

inductive ctxSubset : Ctx → Ctx → Type 
| nil : ctxSubset [] Γ 
| cons : (n ε Γ') → ctxSubset Γ Γ' → ctxSubset (n:A , Γ) Γ' 

notation Γ " ⊆ " Γ' => ctxSubset Γ Γ' 
notation Γ" ∼ "Γ' => (Γ ⊆ Γ') × (Γ' ⊆ Γ)

inductive Term : Type
| var : Nat → Term                  -- variable
| abs : Nat → Term → Term           -- lambda abstraction
| app : Term → Term → Term          -- application
| subst : Nat → Term → Term → Term  -- variable substitution

notation "$"n  => Term.var n
notation "λ("n")."t => Term.abs n t
notation "("t₁")("t₂")" => Term.app t₁ t₂ 
notation t"["x"//"u"]" => Term.subst x u t

namespace Term
#check $5 
#check λ(4).$5
#check (λ(4).$5)($7)

inductive Deduction : Ctx → Term → Typ → Type 
-- n ⊢ n  for any variables --
| var (n : Nat) (A : Typ) : Deduction (n:A , []) ($ n) A

--     Γ ⊢ t:A 
    -------------
--  (n , Γ) ⊢ t:A 
| weak  (n : Nat) (Γ : Ctx) (A : Typ) 
        : (n ¬ε Γ) 
        → Deduction Γ t A 
        → Deduction (n:B , Γ) t A 

--  n₁ , n₂ , Γ  ⊢ t:A 
    ------------------
--  n₂ , n₁ , Γ ⊢ t:A 
| comm {Γ : Ctx} {n₁ n₂ : Nat} {A₁ A₂ : Typ} {t : Term} 
        : Deduction (n₁:A₁ , n₂:A₂ , Γ) t A 
        → Deduction (n₂:A₂ , n₁:A₁ , Γ) t A

--  n + Γ ⊢ n:A  Γ ⊢ t:B 
    --------------------
--    Γ ⊢ λ n.t : A->B
| abs (n: Nat) (Γ : Ctx) (A B : Typ) 
        : Deduction (n:A , Γ) ($ n) A 
        → Deduction Γ t B 
        → Deduction Γ (λ(n).t) (A->B)

--  Γ ⊢ t₁ : A->B     Γ ⊢ t₂ : A
    ----------------------------
--          Γ ⊢ t₁ t₂ : B
| app (n : Nat) (Γ : Ctx) (t₁ t₂ : Term)
        : Deduction Γ t₁ (A->B) 
        → Deduction Γ t₂ A 
        → Deduction Γ ((t₁)(t₂)) B

--  n, Γ ⊢ t : B      Γ ⊢ u : A
    ---------------------------
--        Γ ⊢ t[n // u] : B 
| subst (n : Nat) (Γ : Ctx) (t u : Term) (A B : Typ)
        : Deduction (n:A,Γ) t B
        → Deduction Γ u A
        → Deduction Γ (t[n // u]) B

-- WARNING, This is "\:" not just ":" --
notation Γ " ⊢ " t " ∶ " A => Deduction Γ t A 
namespace Deduction

theorem eqCtxEqDeduction {Γ Γ' : Ctx} : (Γ ∼ Γ') → (Γ ⊢ t ∶ A) → (Γ' ⊢ t ∶ A) := by 
  intro d₁ d₂ 
  induction d₂ 
  case var n B => 
    cases d₁
    case mk fst snd => 
      cases snd 
      case nil => contradiction 
      case cons n₁ Γ₁ B₁ h₁ h₂ => 
        have : B = B₁ := by sorry 
        rw [this]
        cases h₁ 
        case init => 
          induction Γ₁ 
          case nil => apply Deduction.var
          case cons n₂ B₂ Γ₂ h₃ => sorry
        case cons => contradiction 
  case weak t₁ B₁ n₁ Γ₁ B₂ h₁ h₂ h₃ => 
    apply h₃ 
    constructor 
    . cases d₁.1 
      case fst.cons => assumption
    . cases d₁.2 
      case snd.nil => apply ctxSubset.nil 
      case snd.cons n₂ Γ₂ A₂ iH iH₁ => sorry
  case comm A₁ Γ₁ n₂ n₃ B₁ B₂ t₁ h₁ h₂  => 
    apply h₂ 
    constructor 
    case fst => 
      cases d₁.2 
      case nil => 
        apply ctxSubset.cons 
        sorry
      case cons n₅ Γ₅ B₅ hh hh₁ => sorry
    case snd => sorry
      


-- If a weakest context is valid, then a strongest one remains valid --
theorem weakValidCtx (Γ : Ctx) (n₁ : Nat) (A₁ : Typ) : validCtx (n₁:A₁ , Γ) → validCtx Γ  := by 
  intro d 
  cases d 
  case cons A₂ h₁ => assumption

-- Contexts remain valid if we commute their variables ( this should not provable in dependent type theory ! ) --
theorem commValidCtx {Γ : Ctx} {n₁ n₂ : Nat} {A₁ A₂ : Typ} : validCtx (n₁:A₁ , n₂:A₂ , Γ ) → validCtx (n₂:A₂ , n₁:A₁ , Γ ) := by
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
    case a.a => exact weakValidCtx Γ n₂ A₂ (weakValidCtx (n₂:A₂ , Γ) n₁ A₁ d)
    
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
        case init => exact inCtx.init Γ₁ n₁ B₂ 
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
  case subst => sorry
 
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
  case subst => sorry
    
--Any term can be constructed no matter the type if we allow free context --
example {A B : Typ} : Σ Γ : Ctx , Σ t : Term , (Γ ⊢ t ∶ A->B->A) := by
  let Γ := (0:A->B->A , [])
  let t := $0
  have p : Γ ⊢ t ∶ A->B->A := Deduction.var 0 (A->B->A)
  exact ⟨ Γ , ⟨ t , p⟩ ⟩ 

-- The story change if we only allow a restricted context, here we need a more intense derivation --
example {A B : Typ} : Σ t : Term , ((0:B->A , 1:A , []) ⊢ t ∶ A->B->A) := by
  constructor 
  case fst => exact λ(1).$0
  case snd => 
    apply Deduction.comm 
    apply Deduction.weak 
    . intro d ; contradiction
    . apply Deduction.abs 
      . apply Deduction.comm 
        apply Deduction.weak 
        . intro d₁ 
          contradiction 
        . apply Deduction.var
      . apply Deduction.var

-- We can define a well formed term predicate now --
def wellFormedTerm (t : Term) : Type := (Σ Γ : Ctx, Σ A : Typ, (Γ ⊢ t ∶ A))

-- Let us see an example. Here we prove that λ x₀.x₁ is well formed by exhibiting the variables x₀ , x₁ of type base and lambda abstracting. The procedure to prove that a term is well formed forces us to make a choice of types for the variables --
def p₁ : wellFormedTerm  (λ(0).($1)) := by 
  constructor 
  case fst => exact 1:base , []
  case snd => 
    constructor
    case fst => exact base->base 
    case snd => 
      apply Deduction.abs
      . apply Deduction.comm 
        apply Deduction.weak 
        . intro d 
          contradiction 
        . apply Deduction.var 
      . apply Deduction.var

-- We can now extract a deduction from a well formed term --
def ded₁ : (1:base, []) ⊢ (λ(0).($1)) ∶ base->base := p₁.2.2
#check ded₁ 

-- We now ready to define the reductions --
inductive Reduction : Term → Term → Type
| β (n : Nat) (t u : Term) (A B : Typ) : Reduction (λ(n).t)(u) (t[n // u])

notation t₁ "~>₁" t₂ => Reduction t₁ t₂ 

theorem eqCtxSymm : (Γ ∼ Γ') → (Γ' ∼ Γ) := by sorry
theorem th2 : (Γ ∼ Γ') → validCtx Γ → validCtx Γ' := by 
  sorry
theorem th1 : (n:A,n₁:A₂,n₂:A₃,Γ₁) ∼ (n:A,n₂:A₃,n₁:A₂,Γ₁) := by 
  sorry
-- There must be a better way to handle this without going full blown lists --

theorem invAbs (Γ : Ctx) (t q : Term) (n : Nat) (A B C :Typ) (d₁ : t = λ(n).q) (d₂ : C = A->B) : (Γ ⊢ t ∶ C) → validCtx (n:A, Γ) → ((n:A, Γ) ⊢ q ∶ B) := by
  intro d₃ d₄ 
  induction  d₃ 
  case var n D => contradiction 
  case weak t₁ A₁ n₁ Γ₁ A₂ h₁ _ h₃ =>
    apply Deduction.comm 
    apply Deduction.weak 
    . intro d₅ 
      cases d₄ 
      case a.a.cons iH₁ iH₂ => 
        apply iH₂ 
        cases d₅ 
        case init => apply inCtx.init 
        case cons iH₃ => 
          cases iH₁ 
          case cons iH₄ =>
            have : false = true := iH₄ iH₃ 
            contradiction 
    . apply h₃ 
      . exact d₁ 
      . exact d₂ 
      . apply validCtx.cons 
        . intro d₅ 
          cases d₄ ; case a.a.d₄.a.cons iH₁ iH₂ => apply iH₂ ; apply inCtx.cons ; assumption
        . cases d₄ ; case a.a.d₄.a iH₁ iH₂ => cases iH₁ ; assumption 
  case comm A₁ Γ₁ n₁ n₂ A₂ A₃ t₃ _ h₂ => 
    have that : (n:A,n₁:A₂,n₂:A₃,Γ₁) ∼ (n:A,n₂:A₃,n₁:A₂,Γ₁) := th1        
    have thus : validCtx (n:A,n₁:A₂,n₂:A₃,Γ₁) := by 
      exact th2 (eqCtxSymm that) d₄ 
    have : (n:A,n₁:A₂,n₂:A₃,Γ₁) ⊢ q ∶ B := @h₂ d₁ d₂ thus 
    exact eqCtxEqDeduction that this
  case app => contradiction
  case subst => contradiction
  case abs t₂ n₁ Γ₁ B₁ B₂ h₁ h₂ _ _ =>
    have thus₁ : t₂ = q := by injection d₁; assumption
    have thus₂ : n₁  = n := by injection d₁; assumption
    have that₁ : B₂ = B := by injection d₂; assumption
    have that₂  : B₁ = A := by injection d₂; assumption
    rw [← thus₁]
    rw [← that₁]
    rw [← thus₂]
    rw [← that₂]
    apply Deduction.weak 
    . cases (ctxSoundness h₁)
      case a.cons => assumption
    . assumption
    

variable (B C : Typ)
-- We verify some basic properties of β - reduction --
theorem β_PreserveTypes (Γ : Ctx) (t₁ : Term) (A : Typ) 
                        : (Γ ⊢ t₁ ∶ A) → (t₂ : Term) → (t₁ ~>₁ t₂) → (Γ ⊢ t₂ ∶ A) := by 
    intro d
    induction d 
    case var n A₁ => 
      intro t₂ d₁ 
      contradiction
    case weak t₃ A₁ n₁ Γ₁ A₂ h₁ h₂ h₃ =>
      intro t₄ d₂ 
      apply Deduction.weak
      . assumption
      . exact h₃ t₄ d₂ 
    case comm A₁ Γ₁ n₁ n₂ A₂ A₃ t₅ h₁ h₂ => 
      intro t₆ d₂ 
      apply Deduction.comm 
      exact h₂ t₆ d₂ 
    case abs t₅ n₁ Γ₁ A₁ A₂ h₁ h₂ h₃ h₄ =>
      intro t₆ d₁ 
      sorry 
    case app A₁ A₂ n₁ Γ₁ t₅ t₆ h₁ h₂ h₃ h₄ =>
      intro t₇ d₁ 
      sorry 
    case subst n₁ Γ₁ t₅ u A₂ A₃ h₁ h₂ h₃ h₅ =>
      intro t₆ d₁ 
      sorry
