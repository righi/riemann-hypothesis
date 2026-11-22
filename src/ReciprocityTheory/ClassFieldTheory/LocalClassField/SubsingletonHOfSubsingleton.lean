module

public import Mathlib
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.HomFInjective
public import ReciprocityTheory.GroupCohomology.ResNormalHolds
public import ReciprocityTheory.GroupCohomology.Shapiro

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2

open ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationRestrictionInvariants ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {G' : Type u} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']

end

end ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
