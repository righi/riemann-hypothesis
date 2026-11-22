import Mathlib
import ReciprocityTheory.NeutralLocalFields.Reciprocity
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecDefs

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ValuativeRel Function Filter Topology

section

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharZero K]
  (p : ℕ) [Fact p.Prime]

theorem transportRatHom_apply (x : WithVal (Rat.padicValuation p)) :
    transportRatHom p K x = ((WithVal.equiv (Rat.padicValuation p) x : ℚ) : K) := rfl

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
