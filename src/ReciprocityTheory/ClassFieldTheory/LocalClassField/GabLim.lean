module

public import Mathlib
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecDefs
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

open Topology
open scoped commutatorElement

variable {p K L}

theorem subG_sup_eq_inf (L L' : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    subG p K (L ⊔ L') = subG p K L ⊓ subG p K L' := by
  refine le_antisymm (le_inf (subG_anti le_sup_left) (subG_anti le_sup_right)) fun σ hσ => ?_
  have hle : L ⊔ L' ≤ (IntermediateField.fixedField (Subgroup.zpowers σ)).restrictScalars ℚ_[p] := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · rw [IntermediateField.mem_restrictScalars, IntermediateField.mem_fixedField_iff]
      intro τ hτ
      exact (Subgroup.zpowers_le.2 hσ.1 : Subgroup.zpowers σ ≤ subG p K L) hτ x hx
    · rw [IntermediateField.mem_restrictScalars, IntermediateField.mem_fixedField_iff]
      intro τ hτ
      exact (Subgroup.zpowers_le.2 hσ.2 : Subgroup.zpowers σ ≤ subG p K L') hτ x hx
  intro x hx
  have := hle hx
  rw [IntermediateField.mem_restrictScalars, IntermediateField.mem_fixedField_iff] at this
  exact this σ (Subgroup.mem_zpowers σ)

theorem IsAbLK.sup {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : IsAbLK p K L) (h' : IsAbLK p K L') : IsAbLK p K (L ⊔ L') := by
  refine ⟨h.le.trans le_sup_left, ?_, ?_⟩
  · have := h.fin
    have := h'.fin
    exact IntermediateField.finiteDimensional_sup L L'
  · rw [subG_sup_eq_inf]
    exact le_inf h.comm h'.comm

end ReciprocityTheory.DiscreteGroups.LocalClassField
