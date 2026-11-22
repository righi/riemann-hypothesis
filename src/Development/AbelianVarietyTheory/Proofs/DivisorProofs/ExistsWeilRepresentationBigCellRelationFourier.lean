import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCharacterAbsScalarBasicProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapLinearEquivAddHaarLocalFieldStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussIntegralNormFormScaledEqSignAbsInv
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BicharacterFourierTransformTwiceEqPosSmulReflect

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

noncomputable section

namespace GlobalTheory.KSp.WeylCellRel

variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {ν : Type} [Fintype ν] [DecidableEq ν]

theorem mat_mul (p q : UG c (stdJ ν E)) : mat c (p * q) = mat c p * mat c q := rfl

theorem mat_weyl_inv : mat c (weyl c ν)⁻¹ = -stdJ ν E := rfl

theorem mat_unip_inv (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b) : mat c (unip c b hb)⁻¹ = fromBlocks 1 (-b) 0 1 := rfl

theorem mat_weyl : mat c (weyl c ν) = fromBlocks 0 1 (-1) 0 := rfl

theorem mat_levi (hc : ∀ z, c (c z) = z) (a : GL ν E) :
    mat c (levi c hc a) = fromBlocks (a : Matrix ν ν E) 0 0 (((a⁻¹ : GL ν E) : Matrix ν ν E).map c)ᵀ := rfl

theorem mat_unip (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b) : mat c (unip c b hb) = fromBlocks 1 b 0 1 := rfl

end GlobalTheory.KSp.WeylCellRel

end
