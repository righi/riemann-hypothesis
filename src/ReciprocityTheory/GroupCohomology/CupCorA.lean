import ReciprocityTheory.GroupCohomology.ContinuousContractNth

namespace ReciprocityTheory.Coh.CCA

open ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

section Retr

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G)

theorem retr_spec (g : G) : (retr U g : G) = g * (rep U g)⁻¹ := rfl

instance finite_rightRel [U.FiniteIndex] : Finite (Quotient (QuotientGroup.rightRel U)) :=
  Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel U).symm

end Retr

end

end ReciprocityTheory.Coh.CCA
