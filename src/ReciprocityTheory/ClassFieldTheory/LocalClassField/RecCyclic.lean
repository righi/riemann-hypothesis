module

public import Mathlib
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecPairDefs
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecPair
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.NormOpen
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.CyclicBr
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.EqZeroOfMemBrKerOfCoprime
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecCyclicB

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

end ReciprocityTheory.DiscreteGroups.LocalClassField
