module

public import ReciprocityTheory.GroupCohomology.CupCorA

@[expose] public section

namespace ReciprocityTheory.Coh.CCA

open ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

section Leibniz

variable {R : Type u} [CommRing R] {X V W Z : Type u} [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W] [AddCommGroup Z] [Module R Z]

end Leibniz

section PartialProd

end PartialProd

section Homz

variable {R : Type u} [CommRing R]

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {M N P : TRep R G}
  (U : Subgroup G) [U.FiniteIndex]

end Homz

section SlopeTestRemainingChoices

variable {R : Type u} [CommRing R]

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G)

variable [U.FiniteIndex]

end SlopeTestRemainingChoices

end

end ReciprocityTheory.Coh.CCA
