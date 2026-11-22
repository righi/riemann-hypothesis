import ReciprocityTheory.GroupCohomology.CupConnRightStatement
import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal

noncomputable section

universe u

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

section S3
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
theorem cochain_add_val (M : TRep R G) (n : ℕ) (x y : M.coch.X n) : (x + y).1 = x.1 + y.1 := rfl
theorem cochain_smul_val (M : TRep R G) (n : ℕ) (r : R) (x : M.coch.X n) : (r • x).1 = r • x.1 := rfl
theorem cochain_zero_val (M : TRep R G) (n : ℕ) : (0 : M.coch.X n).1 = 0 := rfl

theorem cupCoch_val {M N P : TRep R G} (b : Pairing M N P) (p q : ℕ) (x : M.coch.X p) (y : N.coch.X q) :
    (cupCoch b p q x y).1 = cupFun b p q x.1 y.1 := rfl

theorem cochain_differential_val (M : TRep R G) (n : ℕ) (z : M.coch.X n) : (M.coch.d n z).1 = dn M.rho n z.1 := rfl

end S3

end

end ReciprocityTheory.Coh
