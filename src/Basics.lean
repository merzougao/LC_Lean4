

inductive Typ : Type
  | base : Typ
  | arrow : Typ → Typ → Typ

namespace Typ


inductive Ctx : Type
  | nil   : Ctx
  | cons  : Nat → Typ → Ctx → Ctx 

namespace Ctx

def ctx₁ : Ctx := cons 2 base nil
#check ctx₁ 
#eval ctx₁ 


end Ctx
end Typ
