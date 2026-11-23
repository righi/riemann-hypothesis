module

public import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
public import Mathlib.RingTheory.Valuation.RamificationGroup
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ

@[expose] public section

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

def HasGoodReduction (A : Over (Sp K)) [GrpObj A] : Prop :=
  ∃ (G : Over (Sp R)) (_ : GrpObj G), IsAbelianScheme G ∧
    ∃ e : (Over.pullback (spMap (algebraMap R K))).obj G ≅ A, IsMonHom e.hom

def HasPotentialGoodReduction (A : Over (Sp K)) [GrpObj A] : Prop :=
  ∃ (L W : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (_ : CommRing W) (_ : IsDomain W)
    (_ : IsDiscreteValuationRing W) (_ : Algebra W L) (_ : IsFractionRing W L),
    IsAbove R K (algebraMap W L).range ∧
      HasGoodReduction W L ((Over.pullback (spMap (algebraMap K L))).obj A)

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

theorem specAut_one : specAut (1 : Ω ≃ₐ[K] Ω) = 𝟙 _ :=
  Over.OverMorphism.ext (Spec.map_id (CommRingCat.of Ω))

theorem specAut_mul (σ τ : Ω ≃ₐ[K] Ω) : specAut (σ * τ) = specAut σ ≫ specAut τ :=
  Over.OverMorphism.ext (by
    change spMap _ = spMap _ ≫ spMap _
    rw [← Spec.map_comp]
    rfl)

variable (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A]

def galPts (σ : Ω ≃ₐ[K] Ω) : (ptOver K Ω ⟶ A) →* (ptOver K Ω ⟶ A) :=
  MonoidHom.mk' (fun x => specAut σ ≫ x) fun x y => MonObj.comp_mul _ x y

def galTate (l : ℕ) [Fact l.Prime] : (Ω ≃ₐ[K] Ω) →* Module.End ℤ_[l] (Tate l (ptOver K Ω ⟶ A)) where
  toFun σ := Tate.map l (galPts A σ)
  map_one' := LinearMap.ext fun t => Tate.ext fun n => by
    change specAut 1 ≫ t.lev n = t.lev n
    rw [specAut_one, Category.id_comp]
  map_mul' σ τ := LinearMap.ext fun t => Tate.ext fun n => by
    change specAut (σ * τ) ≫ t.lev n = specAut σ ≫ specAut τ ≫ t.lev n
    rw [specAut_mul, Category.assoc]

variable (K) in
def inertia (V : ValuationSubring Ω) : Subgroup (Ω ≃ₐ[K] Ω) :=
  (V.inertiaSubgroup K).map (V.decompositionSubgroup K).subtype

def TorsionUnramified (V : ValuationSubring Ω) (m : ℕ) : Prop :=
  ∀ σ ∈ inertia K V, ∀ x : ptOver K Ω ⟶ A, x ^ m = 1 → galPts A σ x = x

def TateUnramified (V : ValuationSubring Ω) (l : ℕ) [Fact l.Prime] : Prop :=
  ∀ σ ∈ inertia K V, galTate A l σ = 1

end Galois

def HasCMBy {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (F : Type) [Field F] [NumberField F] : Prop :=
  (∃ d : ℕ, SmoothOfRelativeDimension d A.hom ∧ Module.finrank ℚ F = 2 * d) ∧
    ∃ (O : Type) (_ : CommRing O) (_ : Algebra O F) (_ : IsFractionRing O F), Nonempty (OAct O A)

end AbVarRed

open AbVarRed IsLocalRing

def NeronOggShafarevichSt : Prop :=
  ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)]
    [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (V : ValuationSubring Ω), IsAbove R K V.toSubring →
    ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
      List.TFAE [HasGoodReduction R K A,
        ∀ m : ℕ, (m : ResidueField R) ≠ 0 → TorsionUnramified A V m,
        {m : ℕ | (m : ResidueField R) ≠ 0 ∧ TorsionUnramified A V m}.Infinite,
        ∃ (l : ℕ) (_ : Fact l.Prime), (l : ResidueField R) ≠ 0 ∧ TateUnramified A V l]

def PotentialGoodReductionSt : Prop :=
  ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)]
    [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (V : ValuationSubring Ω), IsAbove R K V.toSubring →
    ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (l : ℕ) [Fact l.Prime], (l : ResidueField R) ≠ 0 →
      (HasPotentialGoodReduction R K A ↔ (galTate A l '' (inertia K V : Set (Ω ≃ₐ[K] Ω))).Finite)

def CMPotentialGoodReductionSt : Prop :=
  ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Finite (ResidueField R)]
    [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A →
    ∀ (F : Type) [Field F] [NumberField F], HasCMBy A F → HasPotentialGoodReduction R K A

def SerreTateGoodReductionSt : Prop :=
  NeronOggShafarevichSt ∧ PotentialGoodReductionSt ∧ CMPotentialGoodReductionSt

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

end AbVarRed

section Consequences

variable {R K Ω : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
  [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] {V : ValuationSubring Ω}
  {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A]

end Consequences

namespace AbVarRed

open GlobalTheory.WeierstrassCurve

theorem factPrimeFive : Fact (Nat.Prime 5) := ⟨by norm_num⟩

attribute [local instance] factPrimeFive

end AbVarRed

end GlobalTheory.Published
