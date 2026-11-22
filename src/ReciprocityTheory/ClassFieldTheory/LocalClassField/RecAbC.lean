module

public import Mathlib
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecPairDefs
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecPair
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecCyclic
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecFunct
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.GabLim
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.NormOpen

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function
open scoped commutatorElement

variable {p : ℕ} [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}

end ReciprocityTheory.DiscreteGroups.LocalClassField
