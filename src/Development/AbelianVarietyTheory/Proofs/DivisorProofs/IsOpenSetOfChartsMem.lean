module

public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.ProjLineOpen
open GlobalTheory.ProjSpace

variable (R : Type) [CommRing R]

def vec (i : Fin 2) : Fin 2 → Polynomial R := fun j => if j = i then 1 else Polynomial.X

theorem span_vec (i : Fin 2) : Ideal.span (Set.range (vec R i)) = ⊤ :=
  Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, by simp [vec]⟩) isUnit_one

def cmap (i : Fin 2) : Sp (Polynomial R) ⟶ PSpace R 1 := pt Polynomial.C (vec R i) (span_vec R i)

def toPoly (i : Fin 2) : MvPolynomial {j : Fin 2 // j ≠ i} R →+* Polynomial R :=
  MvPolynomial.eval₂Hom Polynomial.C fun _ => Polynomial.X

theorem ne_rev (i : Fin 2) : Fin.rev i ≠ i := by fin_cases i <;> decide

instance (i : Fin 2) : Subsingleton {j : Fin 2 // j ≠ i} :=
  ⟨fun a b => Subtype.ext (Fin.ext (by
    have h1 := Fin.val_ne_of_ne a.2; have h2 := Fin.val_ne_of_ne b.2
    have := a.1.2; have := b.1.2; have := i.2; omega))⟩

def fromPoly (i : Fin 2) : Polynomial R →+* MvPolynomial {j : Fin 2 // j ≠ i} R :=
  Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X ⟨Fin.rev i, ne_rev i⟩)

def polyEquiv (i : Fin 2) : MvPolynomial {j : Fin 2 // j ≠ i} R ≃+* Polynomial R :=
  RingEquiv.ofRingHom (toPoly R i) (fromPoly R i)
    (Polynomial.ringHom_ext (fun r => by simp [fromPoly, toPoly]) (by simp [fromPoly, toPoly]))
    (MvPolynomial.ringHom_ext (fun r => by simp [fromPoly, toPoly]) (fun t => by
      simp [fromPoly, toPoly]; exact congrArg _ (Subsingleton.elim _ _)))

instance (i : Fin 2) : IsIso (spMap (toPoly R i)) :=
  inferInstanceAs (IsIso (Spec.map (polyEquiv R i).toCommRingCatIso.hom))

theorem toPoly_dehom (i : Fin 2) :
    (toPoly R i).comp (RingHomClass.toRingHom (dehom R 1 i)) =
      MvPolynomial.eval₂Hom Polynomial.C (vec R i) := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
  · simp [toPoly]
  · by_cases h : j = i
    · subst h; simp [vec]
    · have := dehom_X_of_ne R 1 i ⟨j, h⟩
      simp only [RingHom.comp_apply, RingHom.coe_coe] at this ⊢
      rw [this]; simp [toPoly, vec, h]

theorem chartι_eq (i : Fin 2) : spMap (toPoly R i) ≫ chartι R 1 i = cmap R i := by
  have hu : IsUnit (MvPolynomial.eval₂Hom Polynomial.C (vec R i) (MvPolynomial.X i)) := by
    simp [vec]
  rw [cmap, pt, ProjPoint.ofHom_eq_awayι _ _ _ one_pos (X_mem R 1 i) hu, chartι, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 3
  refine ProjPoint.eq_awayLift _ _ hu (X_mem R 1 i) _ fun n a ha => ?_
  rw [RingHom.comp_apply, awayToPoly_mk R 1 i n a ha]
  have := congrArg (fun φ => φ a) (toPoly_dehom R i)
  simp only [RingHom.comp_apply, RingHom.coe_coe] at this
  rw [this]
  simp [vec]

instance (i : Fin 2) : IsOpenImmersion (cmap R i) := by
  rw [← chartι_eq]; infer_instance

end GlobalTheory.ProjLineOpen
