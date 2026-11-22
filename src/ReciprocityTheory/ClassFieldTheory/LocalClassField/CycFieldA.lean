import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.CycDefs
import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecDefs
import ReciprocityTheory.ClassFieldTheory.LocalClassField.NormOpenB

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p}

theorem finiteDimensional_base_field : FiniteDimensional ℚ_[p] (Q0 p) := inferInstance

theorem ramification_mul_inertia_base_field : eK p (Q0 p) * fK p (Q0 p) = 1 := by
  rw [eK_mul_fK p (Q0 p) finiteDimensional_base_field]
  exact IntermediateField.finrank_bot

theorem residue_cardinality_base_field : qK p (Q0 p) = p := by
  rw [qK_eq_pow_fK p (Q0 p) finiteDimensional_base_field, Nat.eq_one_of_mul_eq_one_left ramification_mul_inertia_base_field, pow_one]

end ReciprocityTheory.DiscreteGroups.LocalClassField
