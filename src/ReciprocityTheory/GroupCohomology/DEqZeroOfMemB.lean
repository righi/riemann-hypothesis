module

public import ReciprocityTheory.GroupCohomology.IsTowerLim
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace ReciprocityTheory.Coh

universe u

namespace Cx

variable {R : Type u} [CommRing R] {A B C : Cx R}

theorem Hom.d_f_eq_zero (φ : Hom A B) {n : ℕ} {x : A.X n} (hx : A.d n x = 0) :
    B.d n (φ.f n x) = 0 := by
  rw [← φ.comm, hx, map_zero]

theorem d_add_eq_zero {n : ℕ} {x y : A.X n} (hx : A.d n x = 0) (hy : A.d n y = 0) :
    A.d n (x + y) = 0 := by
  rw [map_add (f := _), hx, hy, add_zero]

theorem d_sub_eq_zero {n : ℕ} {x y : A.X n} (hx : A.d n x = 0) (hy : A.d n y = 0) :
    A.d n (x - y) = 0 := by
  rw [map_sub, hx, hy, sub_zero]

theorem d_smul_eq_zero {n : ℕ} (r : R) {x : A.X n} (hx : A.d n x = 0) : A.d n (r • x) = 0 := by
  rw [map_smul, hx, smul_zero]

@[elab_as_elim]
theorem H_ind {n : ℕ} {P : A.H n → Prop} (h : ∀ x hx, P (A.cls n x hx)) (c : A.H n) : P c := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  exact h z.1 z.2

theorem exists_cls {n : ℕ} (c : A.H n) : ∃ x hx, c = A.cls n x hx := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  exact ⟨z.1, z.2, rfl⟩

@[simp] theorem cls_add {n : ℕ} (x y : A.X n) (hx : A.d n x = 0) (hy : A.d n y = 0) :
    A.cls n x hx + A.cls n y hy = A.cls n (x + y) (d_add_eq_zero hx hy) := rfl

@[simp] theorem cls_smul {n : ℕ} (r : R) (x : A.X n) (hx : A.d n x = 0) :
    r • A.cls n x hx = A.cls n (r • x) (d_smul_eq_zero r hx) := rfl

theorem cls_eq_iff {n : ℕ} {x y : A.X n} (hx : A.d n x = 0) (hy : A.d n y = 0) :
    A.cls n x hx = A.cls n y hy ↔ x - y ∈ A.B n := by
  unfold cls
  rw [Submodule.Quotient.eq]
  exact Iff.rfl

@[simp] theorem cls_eq_zero_iff {n : ℕ} {x : A.X n} (hx : A.d n x = 0) :
    A.cls n x hx = 0 ↔ x ∈ A.B n := by
  unfold cls
  rw [Submodule.Quotient.mk_eq_zero]
  exact Iff.rfl

theorem cls_congr {n : ℕ} {x y : A.X n} (hx : A.d n x = 0) (hy : A.d n y = 0) (h : x = y) :
    A.cls n x hx = A.cls n y hy := by
  subst h
  rfl

theorem mem_B_succ {n : ℕ} {x : A.X (n + 1)} : x ∈ A.B (n + 1) ↔ ∃ y, A.d n y = x := by
  change x ∈ LinearMap.range (A.d n) ↔ _
  exact LinearMap.mem_range

@[simp] theorem Hom.H_cls (φ : Hom A B) {n : ℕ} (x : A.X n) (hx : A.d n x = 0) :
    φ.H n (A.cls n x hx) = B.cls n (φ.f n x) (φ.d_f_eq_zero hx) := rfl

end Cx


end ReciprocityTheory.Coh
