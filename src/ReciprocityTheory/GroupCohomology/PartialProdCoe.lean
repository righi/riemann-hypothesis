import ReciprocityTheory.GroupCohomology.CupConnRightStatement
import ReciprocityTheory.GroupCohomology.ContinuousContractNth

namespace ReciprocityTheory.Coh

namespace CohomologyFunctoriality₂

open ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

section HomLemmas

variable {R : Type u} [CommRing R] {A B C : Cx R}

theorem Hom.H_mk (φ : Hom A B) (n : ℕ) (z : A.Z n) :
    φ.H n (Submodule.Quotient.mk z) = Submodule.Quotient.mk (φ.Z n z) := rfl

end HomLemmas

section Retr

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G)

theorem retr_spec (g : G) : (retr U g : G) = g * (rep U g)⁻¹ := rfl

instance finite_rightRel [U.FiniteIndex] : Finite (Quotient (QuotientGroup.rightRel U)) :=
  Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel U).symm

end Retr

end

end CohomologyFunctoriality₂

end ReciprocityTheory.Coh
