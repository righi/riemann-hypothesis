module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactOpenNormClosedBallQuadraticStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussIntegralNormFormNonNormCancelStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussIntegralQuadraticCharEventuallyConstStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGaussIntegralCompAddEquivRescaleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactOpenSubgroupExhaustionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadExtTopologyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualBicharacterPairingOfSymmBilinFormStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapMulLeftEqNormSmulStatement

@[expose] public section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

noncomputable section

namespace GlobalTheory.KSp.GaussNorm

open GlobalTheory.SplitWeil (cball)

section Ball

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

end Ball

section Polar

variable {F : Type} [Field F] [CharZero F] {E : Type} [Field E] [Algebra F E] {c : E →ₐ[F] E} {δ : E}

end Polar

end GlobalTheory.KSp.GaussNorm

namespace GlobalTheory.KSp

open GlobalTheory.KSp.GaussNorm GlobalTheory.SplitWeil

end GlobalTheory.KSp
