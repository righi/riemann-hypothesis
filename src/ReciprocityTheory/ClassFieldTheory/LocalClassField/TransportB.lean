module

public import Mathlib
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.TransportDefs
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.NormOpen
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.GabLim
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.TransportBA
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.TransportBB
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.TransportBC

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ValuativeRel Function

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] {p : ℕ} [Fact p.Prime]
  (m : Model K p)

end ReciprocityTheory.DiscreteGroups.LocalClassField
