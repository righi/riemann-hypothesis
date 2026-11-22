module

public import ReciprocityTheory.GroupCohomology.ContinuousContractNth
public import ReciprocityTheory.GroupCohomology.HomogExistsStatement

@[expose] public section

namespace ReciprocityTheory.Coh.CCA

open ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

section HomLemmas

variable {R : Type u} [CommRing R] {A B C : Cx R}

end HomLemmas

section Retr

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G)

end Retr

section Norm

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : TRep R G) (U : Subgroup G) [U.FiniteIndex]

variable {M U}

end Norm

end

end ReciprocityTheory.Coh.CCA
