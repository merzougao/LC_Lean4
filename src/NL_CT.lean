import Init.Data.Nat.Basic

inductive Connective : Type
  | and : Connective
  | or : Connective

inductive Formula0 : Type
  | var : Formula0
  | cons : Connective → Formula0 → Formula0 → Formula0


inductive Ctx0 : Type
  | nil : Ctx0
  | cons : Formula0 → Ctx0 → Ctx0

notation f₀ c f₁ => Formula0.cons c f₀ f₁
notation f","Γ => Ctx0.cons f Γ

inductive AtomicSequent : Ctx0 → Formula0 → Type
  | id : AtomicSequent (Formula0.var,nil) Formula0.var

notation Γ "⊩" F => AtomicSequent Γ F

inductive Sequent : Type
  | atomic : (AtomicSequent Γ f) → Sequent
  | cons :  Sequent → (AtomicSequent Γ f) → Sequent





--inductive deduction : Seq_struct → Seq → Type
