module

public import Mathlib
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecCyclicA

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.RecCyc

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable {p : ℕ} [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}

end ReciprocityTheory.DiscreteGroups.LocalClassField.RecCyc
