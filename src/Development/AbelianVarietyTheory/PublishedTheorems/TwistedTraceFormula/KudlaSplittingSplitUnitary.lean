module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory Matrix

namespace GlobalTheory.SplitUnitary

open GlobalTheory.WeilM (UG hTens IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB IsSmoothRep nabs)

section Group

variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)

def stdJ (ν E : Type) [DecidableEq ν] [Field E] : Matrix (ν ⊕ ν) (ν ⊕ ν) E := fromBlocks 0 1 (-1) 0

variable {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

theorem stdJ_mul_stdJ : stdJ ν E * stdJ ν E = -1 := by
  simp [stdJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]

theorem mem_UG_iff (g : GL (ν ⊕ ν) E) :
    g ∈ UG c (stdJ ν E) ↔
      (g : Matrix (ν ⊕ ν) (ν ⊕ ν) E) * stdJ ν E * ((g : Matrix (ν ⊕ ν) (ν ⊕ ν) E).map c)ᵀ = stdJ ν E := by
  have hT : (stdJ ν E)ᵀ = -stdJ ν E := by simp [stdJ, fromBlocks_transpose, fromBlocks_neg]
  have key : ∀ A B : Matrix (ν ⊕ ν) (ν ⊕ ν) E, A * stdJ ν E * B = stdJ ν E → B * stdJ ν E * A = stdJ ν E := by
    intro A B h
    have h1 : A * (stdJ ν E * B * -stdJ ν E) = 1 := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h, Matrix.mul_neg, stdJ_mul_stdJ, neg_neg]
    have h2 := mul_eq_one_comm.mp h1
    calc B * stdJ ν E * A = (stdJ ν E * stdJ ν E) * (B * -stdJ ν E * A) := by
          rw [stdJ_mul_stdJ]; simp
      _ = stdJ ν E * (stdJ ν E * B * -stdJ ν E * A) := by simp only [Matrix.mul_assoc]
      _ = stdJ ν E := by rw [h2, Matrix.mul_one]
  have tr : ∀ A B : Matrix (ν ⊕ ν) (ν ⊕ ν) E, A * stdJ ν E * B = stdJ ν E → Bᵀ * stdJ ν E * Aᵀ = stdJ ν E := by
    intro A B h
    have h1 := congrArg Matrix.transpose h
    rw [transpose_mul, transpose_mul, hT, ← Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul] at h1
    exact neg_injective h1
  constructor
  · intro h
    have h1 := tr _ _ (show (g : Matrix (ν ⊕ ν) (ν ⊕ ν) E)ᵀ * stdJ ν E * (g : Matrix (ν ⊕ ν) (ν ⊕ ν) E).map c = _ from h)
    rw [transpose_transpose] at h1
    exact key _ _ h1
  · intro h
    have h1 := tr _ _ (key _ _ h)
    rw [transpose_transpose] at h1
    exact h1

def levi (hc : ∀ z, c (c z) = z) (a : GL ν E) : UG c (stdJ ν E) :=
  ⟨⟨fromBlocks (a : Matrix ν ν E) 0 0 (((a⁻¹ : GL ν E) : Matrix ν ν E).map c)ᵀ,
    fromBlocks ((a⁻¹ : GL ν E) : Matrix ν ν E) 0 0 ((a : Matrix ν ν E).map c)ᵀ, by
      rw [fromBlocks_multiply, ← transpose_mul, ← Matrix.map_mul (f := c), Units.mul_inv,
        Matrix.map_one _ (map_zero c) (map_one c)]
      simp, by
      rw [fromBlocks_multiply, ← transpose_mul, ← Matrix.map_mul (f := c), Units.inv_mul,
        Matrix.map_one _ (map_zero c) (map_one c)]
      simp⟩, by
    rw [mem_UG_iff]
    have h1 : ∀ A : Matrix ν ν E, (A.map c)ᵀ.map c = Aᵀ := fun A => by ext i j; simp [hc]
    have h0 : (0 : Matrix ν ν E).map c = 0 := Matrix.map_zero _ (map_zero c)
    simp only [stdJ, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, h1, h0, transpose_transpose,
      transpose_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, add_zero, zero_add, Matrix.mul_neg,
      Matrix.neg_mul, neg_zero]
    rw [← transpose_mul, ← Matrix.map_mul (f := c), Units.mul_inv,
      Matrix.map_one _ (map_zero c) (map_one c), transpose_one]⟩

def form (Q : Matrix α α E) (w w' : Matrix α (ν ⊕ ν) E) : F :=
  2⁻¹ * Algebra.trace F E (hTens c Q (stdJ ν E) w w')

def heisFun (ψ : AddChar F ℂ) (Q : Matrix α α E) (w : Matrix α (ν ⊕ ν) E) (φ : Matrix α ν E → ℂ) : Matrix α ν E → ℂ :=
  fun x => ψ (form c Q (fromCols x 0) (fromCols 0 w.toCols₂) +
    2⁻¹ * form c Q (fromCols w.toCols₁ 0) (fromCols 0 w.toCols₂)) * φ (x + w.toCols₁)

end Group

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E)
  {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

theorem continuous_form_left (Q : Matrix α α E) (w' : Matrix α (ν ⊕ ν) E) :
    Continuous fun x : Matrix α ν E => form c Q (fromCols x 0) w' := by
  have h : ∀ e : E, Continuous fun z : E => Algebra.trace F E (z * e) := fun e =>
    IsModuleTopology.continuous_of_linearMap ((Algebra.trace F E).comp (LinearMap.mulRight F e))

  simp only [form, hTens, map_sum, mul_assoc]
  refine continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ => (h _).comp ?_)
  rcases j with j | j
  · exact continuous_id.matrix_elem i j
  · exact continuous_const

theorem heisFun_mem {ψ : AddChar F ℂ} (hψ : Continuous ψ) (Q : Matrix α α E) (w : Matrix α (ν ⊕ ν) E)
    {φ : Matrix α ν E → ℂ} (hφ : φ ∈ SB (Matrix α ν E)) : heisFun c ψ Q w φ ∈ SB (Matrix α ν E) := by
  haveI := IsModuleTopology.topologicalAddGroup F E
  haveI := GlobalTheory.WeilM.nonarch_field F
  have h1 := (GlobalTheory.WeilM.isLocallyConstant_addChar ψ hψ).comp_continuous
    ((continuous_form_left c Q (fromCols 0 w.toCols₂)).add (continuous_const
      (y := 2⁻¹ * form c Q (fromCols w.toCols₁ 0) (fromCols 0 w.toCols₂))))
  exact ⟨h1.mul (hφ.1.comp_continuous (continuous_id.add continuous_const)),
    (hφ.2.comp_homeomorph (Homeomorph.addRight w.toCols₁)).mul_left⟩

def Heisenberg₂ {ψ : AddChar F ℂ} (hψ : Continuous ψ) (Q : Matrix α α E) (w : Matrix α (ν ⊕ ν) E) :
    Module.End ℂ (SB (Matrix α ν E)) where
  toFun φ := ⟨heisFun c ψ Q w φ, heisFun_mem c hψ Q w φ.2⟩
  map_add' φ φ' := Subtype.ext (funext fun x => mul_add _ _ _)
  map_smul' z φ := Subtype.ext (funext fun x => mul_left_comm _ _ _)

theorem heis_apply {ψ : AddChar F ℂ} (hψ : Continuous ψ) (Q : Matrix α α E) (w : Matrix α (ν ⊕ ν) E)
    (φ : SB (Matrix α ν E)) : (Heisenberg₂ c hψ Q w φ : Matrix α ν E → ℂ) = heisFun c ψ Q w φ := rfl

end Local

end GlobalTheory.SplitUnitary

namespace GlobalTheory.Published

open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB IsSmoothRep nabs)
open GlobalTheory.SplitUnitary

def KudlaSplittingSplitUnitary : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E]
    (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ)
    (α ν : Type) [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]
    (Q : Matrix α α E) (_ : IsHerm c Q)
    (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1)
    (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)),
    ∃ ω : Representation ℂ (UG c (stdJ ν E)) (SB (Matrix α ν E)),
      IsSmoothRep ω ∧
      (∀ μ : @Measure (Matrix α ν E) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∀ (g : UG c (stdJ ν E)) (φ : SB (Matrix α ν E)),
          ∫⁻ x, ‖(ω g φ : Matrix α ν E → ℂ) x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖(φ : Matrix α ν E → ℂ) x‖ₑ ^ 2 ∂μ) ∧
      (∀ (g : UG c (stdJ ν E)) (w : Matrix α (ν ⊕ ν) E),
        Heisenberg₂ c hψ Q w * ω g =
          ω g * Heisenberg₂ c hψ Q (w * ((g : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E))) ∧
      ∀ (a : GL ν E) (φ : SB (Matrix α ν E)) (x : Matrix α ν E),
        (ω (levi c hE.invol a) φ : Matrix α ν E → ℂ) x =
          (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
            ((nabs F (Units.map (Algebra.norm F : E →* F) (Matrix.GeneralLinearGroup.det a)) ^
              ((Fintype.card α : ℝ) / 2) : ℝ) : ℂ) *
            (φ : Matrix α ν E → ℂ) (x * (a : Matrix ν ν E))

end GlobalTheory.Published

end
