import Mathlib
import ReciprocityTheory.GroupCohomology.InfRes
import ReciprocityTheory.GroupCohomology.ComapZeroCoboundariesEqBot
import ReciprocityTheory.GroupCohomology.PartialProdCoe

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2

open ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationRestrictionInvariants ReciprocityTheory.Coh.CohomologyFunctoriality₂ ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem cur_sub (M : TRep R G) (x x' : M.coch.X 2) (g h : G) :
    cur M (x - x') g h = cur M x g h - cur M x' g h := rfl

variable (M : TRep R G) (N : Subgroup G)

end

end ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
