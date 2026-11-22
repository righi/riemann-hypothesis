import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
import ReciprocityTheory.NeutralLocalFields.Duality
import ReciprocityTheory.GroupCohomology.FiveTerm
import ReciprocityTheory.GroupCohomology.CupConnRightStatement
import ReciprocityTheory.GroupCohomology.ContinuousContractNth
import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB
import ReciprocityTheory.GroupCohomology.ContractNthCastAddCastSucc
import ReciprocityTheory.GroupCohomology.PrismOpZeroEval
import ReciprocityTheory.GroupCohomology.PartialProdCoe
import ReciprocityTheory.GroupCohomology.CupCorA
import ReciprocityTheory.GroupCohomology.FiberFirstH0Injective
import ReciprocityTheory.GroupCohomology.LowLES
import ReciprocityTheory.GroupCohomology.RankLen
import ReciprocityTheory.GroupCohomology.Localise
import ReciprocityTheory.GroupCohomology.ContinuousRho
import ReciprocityTheory.GroupCohomology.CardLenStatement
import ReciprocityTheory.GroupCohomology.ConnNatHolds
import ReciprocityTheory.GroupCohomology.PairHomFCoeOfId
import ReciprocityTheory.GroupCohomology.InfRes
import ReciprocityTheory.GroupCohomology.FiniteLevel
import ReciprocityTheory.GroupCohomology.Shapiro
import ReciprocityTheory.GroupCohomology.Section
import ReciprocityTheory.GroupCohomology.InfIsoA
import ReciprocityTheory.GroupCohomology.LowHolds
import ReciprocityTheory.GroupCohomology.ShiftA
import ReciprocityTheory.GroupCohomology.ModelComparisonDegreeZeroBijective
import ReciprocityTheory.GroupCohomology.IsLowExists
import ReciprocityTheory.ClassFieldTheory.LocalClassField.QZDefs
import ReciprocityTheory.ClassFieldTheory.LocalClassField.FinCoh
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RestrictedMultiplicativeH1Subsingleton
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsG
import ReciprocityTheory.ClassFieldTheory.LocalClassField.HerbrandB
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnitsHerbrandF
import ReciprocityTheory.ClassFieldTheory.LocalClassField.CurriedCoboundaryEq

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K}

theorem layerInfl_u_val {L L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : L ≤ L') [(subG p K L).Normal]
    [(subG p K L').Normal] (x : (layer p K L).V) : ((layerInfl (K := K) h).u x).1 = x.1 := rfl

end ReciprocityTheory.DiscreteGroups.LocalClassField
