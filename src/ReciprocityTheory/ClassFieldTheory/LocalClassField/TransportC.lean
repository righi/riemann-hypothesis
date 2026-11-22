module

public import Mathlib
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.TransportDefs
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.TransportA
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.TransportB
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecArtin
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Existence

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ValuativeRel Function

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] {p : ℕ} [Fact p.Prime]
  (m : Model K p)

end ReciprocityTheory.DiscreteGroups.LocalClassField
