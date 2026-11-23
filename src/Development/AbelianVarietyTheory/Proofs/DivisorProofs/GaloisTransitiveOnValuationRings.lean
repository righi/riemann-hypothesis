module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsExtraBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemValuationSubringOfIsIntegral
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
import Mathlib.RingTheory.Invariant.Basic
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
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

open scoped nonZeroDivisors

namespace GlobalTheory.ProlongConj

section general

variable {Ω : Type} [Field Ω]

theorem mem_of_isIntegral {R : Type} [CommRing R] [Algebra R Ω] (A : ValuationSubring Ω)
    (hR : ∀ r : R, algebraMap R Ω r ∈ A) {b : Ω} (hb : IsIntegral R b) : b ∈ A := by
  first
  | (rename_i h_1 h_3 h_4; revert Ω h_1 R h_3 h_4 A hR b hb; exact @_root_.GlobalTheory.IntegralInValuationSubring.mem_valuationSubring_of_isIntegral)
  | exact @_root_.GlobalTheory.IntegralInValuationSubring.mem_valuationSubring_of_isIntegral
  | exact _root_.GlobalTheory.IntegralInValuationSubring.mem_valuationSubring_of_isIntegral
  | (apply _root_.GlobalTheory.IntegralInValuationSubring.mem_valuationSubring_of_isIntegral <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralInValuationSubring.mem_valuationSubring_of_isIntegral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralInValuationSubring.mem_valuationSubring_of_isIntegral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralInValuationSubring.mem_valuationSubring_of_isIntegral ..)

variable (S : Type) [CommRing S] [IsDomain S] [IsDedekindDomain S] [Algebra S Ω] [IsFractionRing S Ω]

theorem exists_den (A : ValuationSubring Ω) (hS : ∀ s : S, algebraMap S Ω s ∈ A) {x : Ω} (hx : x ∈ A) :
    ∃ s t : S, A.valuation (algebraMap S Ω s) = 1 ∧ algebraMap S Ω s * x = algebraMap S Ω t := by
  first
  | (rename_i h_1 h_3 h_4 h_5 h_6 h_7; revert Ω h_1 S h_3 h_4 h_5 h_6 h_7 A hS x hx; exact @_root_.GlobalTheory.ClosingLemma.main)
  | exact @_root_.GlobalTheory.ClosingLemma.main
  | exact _root_.GlobalTheory.ClosingLemma.main
  | (apply _root_.GlobalTheory.ClosingLemma.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ClosingLemma.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ClosingLemma.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ClosingLemma.main ..)

theorem le_of_valuation_lt_one_iff {A A' : ValuationSubring Ω} (hS : ∀ s : S, algebraMap S Ω s ∈ A)
    (hS' : ∀ s : S, algebraMap S Ω s ∈ A')
    (h : ∀ s : S, A.valuation (algebraMap S Ω s) < 1 ↔ A'.valuation (algebraMap S Ω s) < 1) :
    A ≤ A' := by
  intro x hx
  obtain ⟨s, t, hs1, e⟩ := exists_den S A hS hx
  have hs0 : algebraMap S Ω s ≠ 0 := by
    intro h0
    rw [h0, Valuation.map_zero] at hs1
    exact zero_ne_one hs1
  have hs1' : A'.valuation (algebraMap S Ω s) = 1 := by
    refine le_antisymm ((A'.valuation_le_one_iff _).mpr (hS' s)) ?_
    rw [← not_lt, ← h s, hs1]
    exact lt_irrefl 1
  have hxt : x = algebraMap S Ω t * (algebraMap S Ω s)⁻¹ := by rw [← e]; field_simp
  rw [← A'.valuation_le_one_iff, hxt, Valuation.map_mul, map_inv₀, hs1', inv_one, _root_.mul_one,
    A'.valuation_le_one_iff]
  exact hS' t

def primeBelow (A : ValuationSubring Ω) (hS : ∀ s : S, algebraMap S Ω s ∈ A) : Ideal S :=
  (IsLocalRing.maximalIdeal A).comap ((algebraMap S Ω).codRestrict A hS)

theorem mem_primeBelow {A : ValuationSubring Ω} (hS : ∀ s : S, algebraMap S Ω s ∈ A) (s : S) :
    s ∈ primeBelow S A hS ↔ A.valuation (algebraMap S Ω s) < 1 :=
  A.valuation_lt_one_iff _

instance isPrime_primeBelow (A : ValuationSubring Ω) (hS : ∀ s : S, algebraMap S Ω s ∈ A) :
    (primeBelow S A hS).IsPrime := by
  unfold primeBelow
  infer_instance

end general

section galois

end galois

end GlobalTheory.ProlongConj
