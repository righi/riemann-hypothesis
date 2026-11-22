import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar

noncomputable section

open MeasureTheory Matrix

namespace GlobalTheory.SplitUnitary

open GlobalTheory.WeilM (UG hTens IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB IsSmoothRep nabs)

section Group

variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)

variable {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

theorem levi_val (hc : ∀ z, c (c z) = z) (a : GL ν E) :
    ((levi c hc a : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) =
      fromBlocks (a : Matrix ν ν E) 0 0 (((a⁻¹ : GL ν E) : Matrix ν ν E).map c)ᵀ := rfl

end Group

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E)
  {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

theorem heis_apply {ψ : AddChar F ℂ} (hψ : Continuous ψ) (Q : Matrix α α E) (w : Matrix α (ν ⊕ ν) E)
    (φ : SB (Matrix α ν E)) : (Heisenberg₂ c hψ Q w φ : Matrix α ν E → ℂ) = heisFun c ψ Q w φ := rfl

end Local

end GlobalTheory.SplitUnitary

namespace GlobalTheory.Published

end GlobalTheory.Published

end
