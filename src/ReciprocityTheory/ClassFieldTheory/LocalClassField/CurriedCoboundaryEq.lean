module

public import Mathlib
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.IsTwoCocycleCoboundary

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2

open ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationRestrictionInvariants ReciprocityTheory.Coh.CohomologyFunctoriality₂ ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable (M : TRep R G) (N : Subgroup G)

end

end ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
