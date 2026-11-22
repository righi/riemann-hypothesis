module

public import Mathlib
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.TransportDefs
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsG
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.ModelC

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ValuativeRel Function ReciprocityTheory.Neutral.Cmp

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] {p : ℕ} [Fact p.Prime] (m : Model K p)

end ReciprocityTheory.DiscreteGroups.LocalClassField
