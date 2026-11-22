module

public import Mathlib
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.TransportBA

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ValuativeRel Function

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] {p : ℕ} [Fact p.Prime] (m : Model K p)

variable {m}

end ReciprocityTheory.DiscreteGroups.LocalClassField
