module

public import Mathlib
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.FinCoh
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.RestrictedMultiplicativeH1Subsingleton
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsG
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnitsHerbrand
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.EqZeroOfResEqZeroOfCoprime
public import ReciprocityTheory.GroupCohomology.FiniteLevel

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

section Cyclic

variable {R : Type} [CommRing R] {C : Type} [Group C] [Fintype C] [TopologicalSpace C] [IsTopologicalGroup C] [DiscreteTopology C]

end Cyclic

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K}

end ReciprocityTheory.DiscreteGroups.LocalClassField
