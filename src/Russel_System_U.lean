

inductive Universe : Type
  | PropU : Universe
  | TypeU : Universe
  | KindU : Universe

inductive in_universe : Universe → Universe → Type
  | Prop_in_Type : in_universe PropU TypeU
  | Type_in_Kind : in_universe TypeU KindU

inductive dependent : Universe → Universe → Type
  | PropProp : dependent PropU PropU
  | TypeProp : dependent TypeU PropU
  | KindProp : dependent KindU PropU
  | TypeType : dependent TypeU TypeU
  | KindType : dependent KindU TypeU

