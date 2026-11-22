module

public import ReciprocityTheory.GroupCohomology.CardLenStatement
public import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB
public import ReciprocityTheory.GroupCohomology.ConnNatHolds
public import ReciprocityTheory.GroupCohomology.PairHomFCoeOfId
public import ReciprocityTheory.GroupCohomology.Shapiro
public import ReciprocityTheory.GroupCohomology.ShiftA

@[expose] public section

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

namespace KernelCokernelKilling

section KillLES

variable {R : Type u} [CommRing R] {A B C : Cx R} {i : Hom A B} {p : Hom B C}
  {δ : ∀ n, C.H n →ₗ[R] A.H (n + 1)}

end KillLES

section KillRep

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

end KillRep

end KernelCokernelKilling

open KernelCokernelKilling

end

end ReciprocityTheory.Coh
