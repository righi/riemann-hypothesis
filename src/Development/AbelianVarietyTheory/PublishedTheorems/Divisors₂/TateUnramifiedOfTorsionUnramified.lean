import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeSchemeOver
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsStandardSmoothOfRelativeDimensionAwayJacobian
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEisensteinCurve
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

namespace AbVarRed

section Reduction

variable (R K : Type) [CommRing R] [Field K] [Algebra R K]

def IsAbove {L : Type} [Field L] [Algebra K L] (V : Subring L) : Prop :=
  V.comap (algebraMap K L) = (algebraMap R K).range

end Reduction

section Galois

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω]

def specAut (σ : Ω ≃ₐ[K] Ω) : ptOver K Ω ⟶ ptOver K Ω :=
  Over.homMk (spMap (σ : Ω →+* Ω)) (by
    change spMap _ ≫ spMap _ = spMap _
    rw [← Spec.map_comp]
    congr 1
    ext x
    simp)

variable (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A]

def galPts (σ : Ω ≃ₐ[K] Ω) : (ptOver K Ω ⟶ A) →* (ptOver K Ω ⟶ A) :=
  MonoidHom.mk' (fun x => specAut σ ≫ x) fun x y => MonObj.comp_mul _ x y

omit [IsCommMonObj A] in
theorem galPts_left (σ : Ω ≃ₐ[K] Ω) (x : ptOver K Ω ⟶ A) :
    (galPts A σ x).left = spMap (σ : Ω →+* Ω) ≫ x.left := rfl

theorem lev_galTate (l : ℕ) [Fact l.Prime] (σ : Ω ≃ₐ[K] Ω) (t : Tate l (ptOver K Ω ⟶ A)) (n : ℕ) :
    (galTate A l σ t).lev n = galPts A σ (t.lev n) := rfl

variable (K) in

def inertia (V : ValuationSubring Ω) : Subgroup (Ω ≃ₐ[K] Ω) :=
  (V.inertiaSubgroup K).map (V.decompositionSubgroup K).subtype

end Galois

end AbVarRed

open AbVarRed IsLocalRing

namespace AbVarRed

theorem mem_inertia_iff {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (V : ValuationSubring Ω) (σ : Ω ≃ₐ[K] Ω) :
    σ ∈ inertia K V ↔ σ • V = V ∧ ∀ x ∈ V, V.valuation (σ x - x) < 1 := by
  have key : ∀ τ : V.decompositionSubgroup K, τ ∈ V.inertiaSubgroup K ↔
      ∀ x ∈ V, V.valuation ((τ : Ω ≃ₐ[K] Ω) x - x) < 1 := fun τ => by
    have h : ∀ x : V, τ • residue V x = residue V x ↔ V.valuation ((τ : Ω ≃ₐ[K] Ω) x - x) < 1 := fun x => by
      rw [← ResidueField.residue_smul, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff,
        ValuationSubring.valuation_lt_one_iff]
      rfl
    rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
    constructor
    · intro e x hx
      exact (h ⟨x, hx⟩).1 (DFunLike.congr_fun e (residue V ⟨x, hx⟩))
    · intro e
      refine RingEquiv.ext fun y => ?_
      obtain ⟨x, rfl⟩ := residue_surjective y
      exact (h x).2 (e x x.2)
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact ⟨τ.2, (key τ).1 hτ⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨σ, h1⟩, (key _).2 h2, rfl⟩

theorem hasGoodReduction_baseChange_iff {K W L : Type} [Field K] [CommRing W] [Field L] [Algebra K L] [Algebra W L]
    (A : Over (Sp K)) [GrpObj A] :
    HasGoodReduction W L ((Over.pullback (spMap (algebraMap K L))).obj A) ↔
      ∃ (G : Over (Sp W)) (_ : GrpObj G), IsAbelianScheme G ∧ GlobalTheory.SS.IsModel (L := L) A G := Iff.rfl

end AbVarRed

namespace AbVarRed

open GlobalTheory.CMCurve GlobalTheory.WeierstrassCurve

theorem factPrimeFive : Fact (Nat.Prime 5) := ⟨by norm_num⟩

attribute [local instance] factPrimeFive

end AbVarRed

end GlobalTheory.Published
