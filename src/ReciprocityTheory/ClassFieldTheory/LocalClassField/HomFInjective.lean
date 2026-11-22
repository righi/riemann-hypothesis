module

public import Mathlib
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.CurriedCoboundaryEq

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2

open ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationRestrictionInvariants ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable (M : TRep R G) (N : Subgroup G) [N.Normal] (Q : TRep R (G ⧸ N)) (P : Pair Q M)

end

end ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
