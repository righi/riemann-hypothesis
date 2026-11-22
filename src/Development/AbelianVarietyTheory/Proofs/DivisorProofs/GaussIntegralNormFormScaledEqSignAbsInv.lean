import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactOpenNormClosedBallQuadratic
import ReciprocityTheory.NeutralLocalFields.Reciprocity
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecDefs
import ReciprocityTheory.ClassFieldTheory.LocalClassField.TransportA
import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic
import ReciprocityTheory.ClassFieldTheory.LocalClassField.NormOpenB
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsG
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.ModelA
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.Inertia
import ReciprocityTheory.ClassFieldTheory.LocalClassField.QZDefs
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
import ReciprocityTheory.ClassFieldTheory.LocalClassField.InflationH2InjectiveOfSameRamification
import ReciprocityTheory.ClassFieldTheory.LocalClassField.HerbrandB
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnitsHerbrandF
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RestrictedMultiplicativeH1Subsingleton
import ReciprocityTheory.ClassFieldTheory.LocalClassField.FinCoh
import ReciprocityTheory.ClassFieldTheory.LocalClassField.CurriedCoboundaryEq
import ReciprocityTheory.GroupCohomology.CupConnRightStatement
import ReciprocityTheory.GroupCohomology.ContinuousContractNth
import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB
import ReciprocityTheory.GroupCohomology.PrismOpZeroEval
import ReciprocityTheory.GroupCohomology.PartialProdCoe
import ReciprocityTheory.GroupCohomology.Shapiro
import ReciprocityTheory.GroupCohomology.FiniteLevel
import ReciprocityTheory.ClassFieldTheory.LocalClassField.InvRes
import ReciprocityTheory.GroupCohomology.ComapZeroCoboundariesEqBot
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecUnr
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecCyclicB
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecFunct
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecAbA
import ReciprocityTheory.ClassFieldTheory.LocalClassField.KummerA
import ReciprocityTheory.ClassFieldTheory.LocalClassField.BaseCase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapLinearEquivAddHaarLocalFieldStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

noncomputable section

namespace GlobalTheory.KSp.GaussNorm

open GlobalTheory.SplitWeil (cball)

section Polar

variable {F : Type} [Field F] [CharZero F] {E : Type} [Field E] [Algebra F E] {c : E →ₐ[F] E} {δ : E}

theorem polar_apply (hE : IsQuad c δ) (x y : E) :
    polar hE x y = Algebra.norm F (x + y) - Algebra.norm F x - Algebra.norm F y := rfl

end Polar

end GlobalTheory.KSp.GaussNorm

namespace GlobalTheory.KSp

end GlobalTheory.KSp
