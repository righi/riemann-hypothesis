module

public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrExtC
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsA
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsB
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrExtA

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh

noncomputable section

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem norm_le_norm_iff_vK_of_pos (he : 0 < eK p K) (x y : Kˣ) :
    ‖((x : K) : PadicAlgCl p)‖ ≤ ‖((y : K) : PadicAlgCl p)‖ ↔ vK p K y ≤ vK p K x := by
  have he' : (0 : ℝ) < eK p K := by positivity
  rw [← Real.logb_le_logb (one_lt_p_real p) (norm_units_pos x) (norm_units_pos y), ← Int.cast_le (R := ℝ),
    vK_spec, vK_spec, neg_le_neg_iff, mul_le_mul_iff_right₀ he']

theorem norm_le_one_iff_vK_of_pos (he : 0 < eK p K) (x : Kˣ) :
    ‖((x : K) : PadicAlgCl p)‖ ≤ 1 ↔ 0 ≤ vK p K x := by
  have h := norm_le_norm_iff_vK_of_pos p K he x 1
  rw [vK_one] at h
  simpa using h

theorem norm_lt_one_iff_vK_of_pos (he : 0 < eK p K) (x : Kˣ) :
    ‖((x : K) : PadicAlgCl p)‖ < 1 ↔ 1 ≤ vK p K x := by
  have h := norm_le_norm_iff_vK_of_pos p K he 1 x
  rw [vK_one] at h
  have h' : (1 : ℝ) ≤ ‖((x : K) : PadicAlgCl p)‖ ↔ vK p K x ≤ 0 := by simpa using h
  rw [← not_le, h']
  omega

theorem norm_le_one_iff_vK (hK : FiniteDimensional ℚ_[p] K) (x : Kˣ) :
    ‖((x : K) : PadicAlgCl p)‖ ≤ 1 ↔ 0 ≤ vK p K x := norm_le_one_iff_vK_of_pos p K (eK_pos p K hK) x

theorem norm_lt_one_iff_vK (hK : FiniteDimensional ℚ_[p] K) (x : Kˣ) :
    ‖((x : K) : PadicAlgCl p)‖ < 1 ↔ 1 ≤ vK p K x := norm_lt_one_iff_vK_of_pos p K (eK_pos p K hK) x

theorem norm_le_norm_iff_vK (hK : FiniteDimensional ℚ_[p] K) (x y : Kˣ) :
    ‖((x : K) : PadicAlgCl p)‖ ≤ ‖((y : K) : PadicAlgCl p)‖ ↔ vK p K y ≤ vK p K x :=
  norm_le_norm_iff_vK_of_pos p K (eK_pos p K hK) x y

theorem vK_p (x : Kˣ) (hx : ((x : K) : PadicAlgCl p) = (p : PadicAlgCl p)) : vK p K x = eK p K := by
  apply Int.cast_injective (α := ℝ)
  rw [vK_spec, hx, logb_norm_p]
  simp

variable {K L}

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
