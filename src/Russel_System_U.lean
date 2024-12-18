

inductive Typ : Type
  | PropU : Typ
  | TypeU : Typ
  | KindU : Typ

inductive Term : Type
  | propTerm : Term
  | typeTerm : Term


inductive Var : Type
  | cons : Nat → Typ → Var

inductive Ctx : Type
  | nil : Ctx
  | cons : Var → Ctx → Ctx

notation "[]" => Ctx.nil
notation x" , "Γ => Ctx.cons x Γ

def Typeof : Term → Typ :=
  sorry

inductive Typing : Ctx → Term → Typ → Type
  | PropInType : Typing nil propTerm TypeU
  | TypeInKind : Typing nil typeTerm KindU
  | var : Typing Γ A s → Typing (Ctx.cons (Var.cons 0 (Typeof A)) Γ) (Var.cons 0) (Typeof A)
