module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open TopologicalSpace

namespace GlobalTheory.SmoothRelDim

theorem smoothOfRelativeDimension_of_generic (R : Type) [CommRing R] [IsDomain R] (X : Over (Sp R))
    [Smooth X.hom] (K : Type) [Field K] (e : R →+* K) (he : Function.Injective e) (g : ℕ)
    (hg : SmoothOfRelativeDimension g (pullback.snd X.hom (spMap e))) :
    SmoothOfRelativeDimension g X.hom := by
  have hdom : IsDominant (spMap e) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (by change RingHom.ker e ≤ _; rw [(RingHom.injective_iff_ker_eq_bot e).1 he]; exact bot_le)⟩
  choose n W hW hd using ReciprocityTheory.ChartRestriction.G.H1.exists_dim X.hom
  have : UniversallyOpen X.hom := UniversallyOpen.of_flat X.hom
  have key : ∀ x, n x = g := fun x => by
    have ho : IsOpen (X.hom.base '' (W x : Set X.left)) := X.hom.isOpenMap _ (W x).isOpen
    obtain ⟨s, ⟨y, hyW, hy⟩, t, rfl⟩ :=
      hdom.denseRange.inter_open_nonempty _ ho ⟨_, x, hW x, rfl⟩
    obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback y t hy
    exact ReciprocityTheory.ChartRestriction.G.H1.dim_base (IsPullback.of_hasPullback X.hom (spMap e)) (hd x) hg z (hz1 ▸ hyW)
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension g) := HasRingHomProperty.instIsZariskiLocalAtSource
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) W
    (top_le_iff.1 fun x _ => Opens.mem_iSup.2 ⟨x, hW x⟩) fun x => key x ▸ hd x

end GlobalTheory.SmoothRelDim
