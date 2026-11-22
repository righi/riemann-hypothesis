module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGLDiagonalCongruentHermitianStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussIntegralDiagonalHermitianFormMatricesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGaussIntegralCompAddEquivRescaleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapTwoSidedMulHaarMatrixQuadraticExtStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMatrixColumnPairingDiagonalNormStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCharacterAbsScalarBasicPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalNormResidueSignMulStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadExtTopologyStatement

@[expose] public section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

noncomputable section

namespace GlobalTheory.KSp.GaussMain

section Scalar

variable {F : Type} [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E]
  (c : E →ₐ[F] E) {δ : E} (hE : IsQuad c δ)

variable {ν : Type} [Fintype ν] [DecidableEq ν]

end Scalar

section Equiv

variable {E : Type} [Field E] [TopologicalSpace E] [IsTopologicalRing E]
  {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

end Equiv

end GlobalTheory.KSp.GaussMain
