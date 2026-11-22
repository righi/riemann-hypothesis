import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactOpenNormClosedBallQuadratic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open Filter Topology

namespace GlobalTheory.KSp.ParNear

variable {E : Type} [Field E] {ν : Type} [Fintype ν] [DecidableEq ν]

variable {F : Type} [Field F] [Algebra F E] (c : E →ₐ[F] E) {α : Type} [Fintype α] [DecidableEq α]

theorem mat_one : mat c (1 : UG c (stdJ ν E)) = 1 := rfl

variable [TopologicalSpace F] [TopologicalSpace E] [IsTopologicalRing E]

end GlobalTheory.KSp.ParNear

