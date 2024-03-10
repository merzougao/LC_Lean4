import Init.Data.Nat.Basic

inductive Connective : Type
  | and : Connective
  | or : Connective

inductive Formula : Type
  | var : Nat → Formula
  | cons : Connective → Formula → Formula → Formula

notation "$" n => Formula.var n

def A : Formula := $ 0
def B : Formula := $ 1


inductive Ctx : Type
  | nil : Ctx
  | cons : Formula → Ctx → Ctx

notation "∅" => Ctx.nil
notation f₀ c f₁ => Formula.cons c f₀ f₁
notation f","Γ => Ctx.cons f Γ

inductive AtomicSequent : Type
  | id : Nat → AtomicSequent
  
notation Γ "⊩" F => AtomicSequent Γ F
#check (A , (B, ∅)) ⊩ A
def Λ : AtomicSequent Γ f := (A , (B, ∅)) ⊩ A

inductive Sequent : Type
  | atomic : (AtomicSequent Γ f) → Sequent
  | cons :  Sequent → (AtomicSequent Γ f) → Sequent






--inductive deduction : Seq_struct → Seq → Type
