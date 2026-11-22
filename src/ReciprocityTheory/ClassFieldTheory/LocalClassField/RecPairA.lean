module

public import Mathlib
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecPairDefs
public import ReciprocityTheory.GroupCohomology.ComapZeroCoboundariesEqBot
public import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable (M : TRep ℤ G)

end General

end ReciprocityTheory.DiscreteGroups.LocalClassField
