import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecDefs
import ReciprocityTheory.ClassFieldTheory.LocalClassField.QZDefs
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
import ReciprocityTheory.ClassFieldTheory.LocalClassField.InflationH2InjectiveOfSameRamification
import ReciprocityTheory.ClassFieldTheory.LocalClassField.HerbrandB
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnitsHerbrandF
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsG
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

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

theorem urOfK_val (a : Kˣ) : (urOfK p K a).1 = ofK p K (Additive.ofMul a) := rfl

end ReciprocityTheory.DiscreteGroups.LocalClassField
