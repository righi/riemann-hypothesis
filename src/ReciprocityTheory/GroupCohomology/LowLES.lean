module

public import ReciprocityTheory.GroupCohomology.TransgressionStatement
public import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB
public import ReciprocityTheory.GroupCohomology.LowHolds
public import ReciprocityTheory.GroupCohomology.LowNat
public import ReciprocityTheory.GroupCohomology.ConnNatHolds
public import ReciprocityTheory.GroupCohomology.PairHomFCoeOfId
public import ReciprocityTheory.GroupCohomology.InfRes
public import ReciprocityTheory.GroupCohomology.ResNormalHolds

@[expose] public section

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal LowDeg

universe u

section SlopeTestRemainingChoices

variable {R : Type u} [CommRing R] {G G' : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']

end SlopeTestRemainingChoices

end ReciprocityTheory.Coh
