module

public import ReciprocityTheory.GroupCohomology.CupConnRightStatement
public import ReciprocityTheory.GroupCohomology.HomogExistsStatement
public import Mathlib.Topology.ContinuousMap.Algebra
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.GroupCohomology.HomogIso
public import ReciprocityTheory.GroupCohomology.PrismOpZeroEval

@[expose] public section

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

section QI

variable {R : Type u} [CommRing R] {A B : Cx R}

end QI

section Push

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {U : Subgroup G} {M : TRep R U} {C : TRep R G} (ev : Pair C M) (hφ : ev.φ = U.subtype)

variable (j : C.V → C(G, M.V)) (hj : Topology.IsEmbedding j) (hjc : ∀ c g, j c g = ev.u (C.rho g c))
  (hr : ∀ f : C(G, M.V), (∀ (x : U) g, f (x * g) = M.rho x (f g)) → f ∈ Set.range j)

end Push

section Coind

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U : Subgroup G) (M : TRep R U)

def coindSub : Submodule R C(G, M.V) where
  carrier := {f | ∀ (x : U) g, f (x * g) = M.rho x (f g)}
  zero_mem' := fun x g => by simp
  add_mem' := fun {a b} ha hb x g => by simp [ha x g, hb x g]
  smul_mem' c a ha x g := by simp [ha x g]

variable {U M}

variable (U M)

instance : ContinuousConstSMul R (coindSub U M) :=
  ⟨fun c => ((continuous_const_smul c).comp continuous_subtype_val).subtype_mk _⟩

variable [LocallyCompactSpace G]

end Coind

end

end ReciprocityTheory.Coh
