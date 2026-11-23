module

public import Mathlib.RingTheory.Length
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace ReciprocityTheory.Coh

noncomputable section

universe u

variable {R : Type u} [CommRing R]

structure Cx (R : Type u) [CommRing R] where
  X : ℕ → Type u
  [acg : ∀ n, AddCommGroup (X n)]
  [mod : ∀ n, Module R (X n)]
  d : ∀ n, X n →ₗ[R] X (n + 1)
  dd : ∀ n x, d (n + 1) (d n x) = 0

attribute [instance] Cx.acg Cx.mod

namespace Cx

def Z (A : Cx R) (n : ℕ) : Submodule R (A.X n) := LinearMap.ker (A.d n)

def B (A : Cx R) : (n : ℕ) → Submodule R (A.X n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (A.d n)

abbrev H (A : Cx R) (n : ℕ) := A.Z n ⧸ (A.B n).comap (A.Z n).subtype

def cls (A : Cx R) (n : ℕ) (x : A.X n) (hx : A.d n x = 0) : A.H n := Submodule.Quotient.mk ⟨x, hx⟩

structure Hom (A B : Cx R) where
  f : ∀ n, A.X n →ₗ[R] B.X n
  comm : ∀ n x, f (n + 1) (A.d n x) = B.d n (f n x)

variable {A B C : Cx R}

def Hom.id (A : Cx R) : Hom A A := ⟨fun _ => LinearMap.id, fun _ _ => rfl⟩

def Hom.comp (ψ : Hom B C) (φ : Hom A B) : Hom A C :=
  ⟨fun n => (ψ.f n).comp (φ.f n), fun n x => by simp [φ.comm, ψ.comm]⟩

def Hom.Z (φ : Hom A B) (n : ℕ) : A.Z n →ₗ[R] B.Z n :=
  (φ.f n).restrict fun x hx => by
    have hx' : A.d n x = 0 := hx
    show B.d n (φ.f n x) = 0
    rw [← φ.comm, hx', map_zero]

def Hom.H (φ : Hom A B) (n : ℕ) : A.H n →ₗ[R] B.H n :=
  Submodule.mapQ _ _ (φ.Z n) fun x hx => by
    cases n with
    | zero =>
      have hx' : x.1 = 0 := hx
      show φ.f 0 x.1 ∈ (⊥ : Submodule R _)
      rw [hx', map_zero]; exact Submodule.zero_mem _
    | succ n =>
      obtain ⟨y, hy⟩ := hx
      refine ⟨φ.f n y, ?_⟩
      show B.d n (φ.f n y) = φ.f (n + 1) x.1
      rw [← φ.comm, hy]; rfl

structure SES (i : Hom A B) (p : Hom B C) : Prop where
  inj : ∀ n, Function.Injective (i.f n)
  exact : ∀ n, Function.Exact (i.f n) (p.f n)
  surj : ∀ n, Function.Surjective (p.f n)

def IsConn (i : Hom A B) (p : Hom B C) (δ : ∀ n, C.H n →ₗ[R] A.H (n + 1)) : Prop :=
  ∀ n (b : B.X n) (a : A.X (n + 1)) (hc : C.d n (p.f n b) = 0) (ha : A.d (n + 1) a = 0),
    B.d n b = i.f (n + 1) a → δ n (C.cls n (p.f n b) hc) = A.cls (n + 1) a ha

structure LES (i : Hom A B) (p : Hom B C) (δ : ∀ n, C.H n →ₗ[R] A.H (n + 1)) : Prop where
  inj : Function.Injective (i.H 0)
  exB : ∀ n, Function.Exact (i.H n) (p.H n)
  exC : ∀ n, Function.Exact (p.H n) (δ n)
  exA : ∀ n, Function.Exact (δ n) (i.H (n + 1))

def FinLen (A : Cx R) (N : ℕ) : Prop :=
  (∀ n, IsFiniteLength R (A.H n)) ∧ ∀ n, N < n → Subsingleton (A.H n)

def chi (A : Cx R) (N : ℕ) : ℤ :=
  ∑ n ∈ Finset.range (N + 1), (-1) ^ n * ((Module.length R (A.H n)).toNat : ℤ)

structure IsTowerLim (A : ℕ → Cx R) (τ : ∀ m, Hom (A (m + 1)) (A m)) (L : Cx R) (π : ∀ m, Hom L (A m)) :
    Prop where
  surj : ∀ m n, Function.Surjective ((τ m).f n)
  compat : ∀ m n x, (τ m).f n ((π (m + 1)).f n x) = (π m).f n x
  ext : ∀ n (x : L.X n), (∀ m, (π m).f n x = 0) → x = 0
  lift : ∀ n (y : ∀ m, (A m).X n), (∀ m, (τ m).f n (y (m + 1)) = y m) → ∃ x, ∀ m, (π m).f n x = y m

end Cx

end

end ReciprocityTheory.Coh
