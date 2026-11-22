module

public import Mathlib
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecPairDefs
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecPair
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.NormOpen
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecPairA
public import ReciprocityTheory.GroupCohomology.CupCor
public import ReciprocityTheory.GroupCohomology.ContractNthCastAddCastSucc
public import ReciprocityTheory.GroupCohomology.ResNormalHolds

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

section general

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

end general

end ReciprocityTheory.DiscreteGroups.LocalClassField
