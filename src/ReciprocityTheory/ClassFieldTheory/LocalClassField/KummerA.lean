module

public import Mathlib
public import ReciprocityTheory.NeutralLocalFields.Duality
public import ReciprocityTheory.GroupCohomology.LowLES

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer

open _root_.Neutral.B1

noncomputable section

section Scalars

variable {R : Type} [CommRing R] {G : Type} [Group G] [TopologicalSpace G]
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
  (rho : Representation R G M) (rho' : Representation ℤ G M) (h : ∀ g m, rho g m = rho' g m)

end Scalars

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ) [NeZero n]

variable {p n}

variable (p n) in
end

end ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer
