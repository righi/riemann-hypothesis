import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
import ReciprocityTheory.ClassFieldTheory.LocalClassField.KummerA
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RestrictedMultiplicativeH1Subsingleton
import ReciprocityTheory.ClassFieldTheory.LocalClassField.FinCoh
import ReciprocityTheory.ClassFieldTheory.LocalClassField.CurriedCoboundaryEq
import ReciprocityTheory.GroupCohomology.CupConnRightStatement
import ReciprocityTheory.GroupCohomology.ContinuousContractNth
import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB
import ReciprocityTheory.GroupCohomology.PrismOpZeroEval
import ReciprocityTheory.GroupCohomology.PartialProdCoe
import ReciprocityTheory.GroupCohomology.Shapiro

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p}

scoped instance discreteTopology_muT (F : IntermediateField ℚ_[p] (PadicAlgCl p)) (l : ℕ) [NeZero l] :
    DiscreteTopology (Kummer.muT p F l).V :=
  inferInstanceAs (DiscreteTopology (ZMod l))

end ReciprocityTheory.DiscreteGroups.LocalClassField
