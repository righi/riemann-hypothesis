module

public import ReciprocityTheory.GroupCohomology.ContinuousContractNth
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

open ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def hcoch (M : TRep R G) (X : Type u) [TopologicalSpace X] [MulAction G X] (n : ℕ) :
    Submodule R ((Fin (n + 1) → X) → M.V) where
  carrier := {F | Continuous F ∧ ∀ (g : G) x, F (fun i => g • x i) = M.rho g (F x)}
  zero_mem' := ⟨continuous_const, fun g x => by simp⟩
  add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun g x => by simp [ha.2, hb.2]⟩
  smul_mem' c a ha := ⟨ha.1.const_smul c, fun g x => by simp [ha.2]⟩

def hd {V X : Type u} [AddCommGroup V] (n : ℕ) (F : (Fin (n + 1) → X) → V) (x : Fin (n + 2) → X) : V :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • F fun j => x (i.succAbove j)

def IsHomog (M : TRep R G) (X : Type u) [TopologicalSpace X] [MulAction G X] (A : Cx R)
    (e : ∀ n, A.X n ≃ₗ[R] hcoch M X n) : Prop :=
  ∀ n a, (e (n + 1) (A.d n a)).1 = hd n (e n a).1

def HomogExistsStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (M : TRep R G) (X : Type u) [TopologicalSpace X] [MulAction G X],
  ∃ A e, IsHomog M X A e

end

end ReciprocityTheory.Coh
