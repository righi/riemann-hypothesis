module

public import ReciprocityTheory.GroupCohomology.CupConnRightStatement
public import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB

@[expose] public section

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal

noncomputable section

universe u

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

section S1
variable {G : Type u} [Group G]

variable {p q : ℕ} (e : p + 1 + q = p + q + 1) (g : Fin (p + q + 1) → G)

end S1

section S2
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
end S2

section S3
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
theorem cochain_add_val (M : TRep R G) (n : ℕ) (x y : M.coch.X n) : (x + y).1 = x.1 + y.1 := rfl
end S3

section S4
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
end S4

section S5

end S5

end

end ReciprocityTheory.Coh
