module

public import ReciprocityTheory.GroupCohomology.CupConnRightStatement
public import ReciprocityTheory.GroupCohomology.HomogExistsStatement

@[expose] public section

namespace ReciprocityTheory.Coh

namespace CohomologyFunctoriality₂

open ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

section HomLemmas

variable {R : Type u} [CommRing R] {A B C : Cx R}

end HomLemmas

section Retr

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G)

theorem retr_spec (g : G) : (retr U g : G) = g * (rep U g)⁻¹ := rfl

end Retr

section Norm

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : TRep R G) (U : Subgroup G) [U.FiniteIndex]

variable {M U}

end Norm

section Incl

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : TRep R G} {U : Subgroup G}

end Incl

section Conj

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

end Conj
end

end CohomologyFunctoriality₂

end ReciprocityTheory.Coh
