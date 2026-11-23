module

public import ReciprocityTheory.GroupCohomology.Shapiro
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
public import ReciprocityTheory.GroupCohomology.ConnNatHolds
public import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB
public import ReciprocityTheory.GroupCohomology.PairHomFCoeOfId

@[expose] public section

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

namespace KernelCokernelKilling

section Disc

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem contAction_of_disc {V : Type u} [AddCommGroup V] [Module R V] [TopologicalSpace V]
    [DiscreteTopology V] (rho : Representation R G V) (h : ∀ v, Continuous fun g => rho g v) :
    ContAction rho :=
  continuous_prod_of_discrete_right.2 h

theorem orbit_cont (B : TRep R G) (v : B.V) : Continuous fun g => B.rho g v :=
  B.cont.comp (f := fun g : G => (g, v)) (continuous_id.prodMk continuous_const)

theorem disc_quot {V : Type u} [AddCommGroup V] [Module R V] [TopologicalSpace V] [DiscreteTopology V]
    (S : Submodule R V) : DiscreteTopology (V ⧸ S) :=
  discreteTopology_iff_forall_isOpen.2 fun _ =>
    (Submodule.isQuotientMap_mkQ S).isOpen_preimage.1 (isOpen_discrete _)

def quotRep (B : TRep R G) [DiscreteTopology B.V] (S : Submodule R B.V)
    (hS : ∀ g, S ≤ S.comap (B.rho g)) : TRep R G where
  V := B.V ⧸ S
  ccs := ⟨fun _ => by have := disc_quot S; exact continuous_of_discreteTopology⟩
  rho := B.rho.quotient S hS
  cont := by
    have := disc_quot S
    refine contAction_of_disc _ fun v => ?_
    induction v using Submodule.Quotient.induction_on with
    | H v => exact (continuous_of_discreteTopology (f := S.mkQ)).comp (orbit_cont B v)

instance (B : TRep R G) [DiscreteTopology B.V] (S : Submodule R B.V) (hS) :
    DiscreteTopology (quotRep B S hS).V := disc_quot S

end Disc

section Triv

variable {R : Type u} [CommRing R] {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Subsingleton H]

end Triv

section ShiftSec

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable [CompactSpace G]

end ShiftSec

section ShiftC

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (M : TRep R G) [DiscreteTopology M.V]

end ShiftC

end KernelCokernelKilling

end

end ReciprocityTheory.Coh
