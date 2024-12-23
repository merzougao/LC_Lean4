

inductive Term : Type
  | PropU : Term
  | TypeU : Term
  | KindU : Term
  | var : Nat → Term
  | prod : Nat → Term → Term → Term
  | app : Term → Term → Term
  | abs : Nat → Term → Term → Term

inductive Relation : Term → Term → Prop
  | pp : Relation PropU PropU
  | tp : Relation TypeU PropU
  | tt : Relation TypeU TypeU
  | kp : Relation KindU PropU
  | kt : Relation KindU TypeU


notation "$"n => Term.var n

inductive Ctx : Type
  | nil : Ctx
  | cons : Nat → Term → Ctx → Ctx

notation "[]" => Ctx.nil
notation n":"t","Γ => Ctx.cons n t Γ

inductive NotInCtx : Nat → Ctx → Type
  | nil : NotInCtx n nil
  | cons : (n ≠ m) → NotInCtx n Γ → NotInCtx m (n : T, Γ')

def Typeof : Term → Term :=
  sorry

def subst : Term → Nat → Term → Term := by
  intro u n t
  cases t
  case PropU => exact Term.PropU
  case TypeU => exact Term.TypeU
  case KindU => exact Term.KindU
  case var m => exact if n = m then u else $ m
  case prod m t₀ t₁ => exact if (n = m) then Term.prod m t₀ t₁ else Term.prod m t₀ (subst u n t₁)
  case abs m t₀ t₁ => exact if (n = m) then Term.abs m t₀ t₁ else Term.abs m t₀ (subst u n t₁)
  case app t₀ t₁ => exact Term.app (subst u n t₀) (subst u n t₁)


inductive Typing : Ctx → Term → Term → Type
  | PropInType : Typing nil propTerm TypeU
  | TypeInKind : Typing nil typeTerm KindU
  | var : NotInCtx n Γ → Typing Γ A s → Typing ( n : (Typeof A) , Γ) ($ n) (Typeof A)
  | weak : NotInCtx n Γ → Typing Γ t T → Typing (n : P , Γ) t T
  | prod : Relation T P → Typing Γ t T → Typing (n : t , Γ) t₂ P → Typing Γ (Term.prod n t t₂) P
  | app : Typing Γ t₀ (Term.prod n T t) → Typing Γ u T → Typing Γ (Term.app t u) (subst u n t₀)
  | abs : Typing Γ (Term.prod n T A) B → Typing (n : T , Γ) t A → Typing Γ (Term.abs n T t) A
