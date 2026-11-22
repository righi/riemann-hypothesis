import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsE

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh

noncomputable section

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem mem_UKi_iff (i : ℕ) (x : Kˣ) :
    x ∈ UKi p K i ↔ x ∈ UK p K ∧ ‖((x : K) : PadicAlgCl p) - 1‖ ≤ (p : ℝ) ^ (- (i : ℝ) / eK p K) := Iff.rfl

theorem norm_pow_uniformiser (hK : FiniteDimensional ℚ_[p] K) {π : Kˣ} (hπ : vK p K π = 1) (i : ℕ) :
    ‖((π : K) : PadicAlgCl p)‖ ^ i = (p : ℝ) ^ (- (i : ℝ) / eK p K) := by
  have h := norm_eq_rpow_vK p K hK (π ^ i)
  rw [vK_pow, hπ, mul_one, Int.cast_natCast, Units.val_pow_eq_pow_val, SubmonoidClass.coe_pow, norm_pow] at h
  exact h

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
