module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.Index

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand

open Function

variable {M : Type*} [AddCommGroup M]

abbrev T (D N : M →+ M) : Type _ := D.ker ⧸ (N.range.addSubgroupOf D.ker)

noncomputable def q (D N : M →+ M) : ℚ := (Nat.card (T D N) : ℚ) / (Nat.card (T N D) : ℚ)

structure SES {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (DA NA : A →+ A) (DB NB : B →+ B) (DC NC : C →+ C) (f : A →+ B) (g : B →+ C) : Prop where
  inj : Injective f
  exact : Function.Exact f g
  surj : Surjective g
  fD : ∀ a, f (DA a) = DB (f a)
  fN : ∀ a, f (NA a) = NB (f a)
  gD : ∀ b, g (DB b) = DC (g b)
  gN : ∀ b, g (NB b) = NC (g b)
  DN : ∀ b, DB (NB b) = 0
  ND : ∀ b, NB (DB b) = 0

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    {DA NA : A →+ A} {DB NB : B →+ B} {DC NC : C →+ C} {f : A →+ B} {g : B →+ C}

theorem SES.swap (h : SES DA NA DB NB DC NC f g) : SES NA DA NB DB NC DC f g :=
  ⟨h.inj, h.exact, h.surj, h.fN, h.fD, h.gN, h.gD, h.ND, h.DN⟩

def Rel (DB : B →+ B) (f : A →+ B) (g : B →+ C) (c : C) (a : A) : Prop := ∃ b, g b = c ∧ f a = DB b

section Count

variable {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]

end Count

end ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
