import Mathlib
import ReciprocityTheory.NeutralLocalFields.Duality
import ReciprocityTheory.GroupCohomology.ContinuousContractNth

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

scoped instance : DiscreteTopology (kbarT p K).V := inferInstanceAs (DiscreteTopology (KbarMult p))

end ReciprocityTheory.DiscreteGroups.LocalClassField
