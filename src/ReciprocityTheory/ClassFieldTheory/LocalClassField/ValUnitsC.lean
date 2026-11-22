import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsB

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh

noncomputable section

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem norm_eq_rpow_vK_of_pos (he : 0 < eK p K) (x : Kˣ) :
    ‖((x : K) : PadicAlgCl p)‖ = (p : ℝ) ^ (- (vK p K x : ℝ) / eK p K) := by
  have he' : (eK p K : ℝ) ≠ 0 := by positivity
  have h1 : - (vK p K x : ℝ) / eK p K = Real.logb p ‖((x : K) : PadicAlgCl p)‖ := by
    rw [vK_spec]; field_simp
  rw [h1, Real.rpow_logb (by linarith [one_lt_p_real p]) (one_lt_p_real p).ne' (norm_units_pos x)]

theorem norm_le_norm_iff_vK_of_pos (he : 0 < eK p K) (x y : Kˣ) :
    ‖((x : K) : PadicAlgCl p)‖ ≤ ‖((y : K) : PadicAlgCl p)‖ ↔ vK p K y ≤ vK p K x := by
  have he' : (0 : ℝ) < eK p K := by positivity
  rw [← Real.logb_le_logb (one_lt_p_real p) (norm_units_pos x) (norm_units_pos y), ← Int.cast_le (R := ℝ),
    vK_spec, vK_spec, neg_le_neg_iff, mul_le_mul_iff_right₀ he']

theorem norm_le_one_iff_vK_of_pos (he : 0 < eK p K) (x : Kˣ) :
    ‖((x : K) : PadicAlgCl p)‖ ≤ 1 ↔ 0 ≤ vK p K x := by
  have h := norm_le_norm_iff_vK_of_pos p K he x 1
  rw [vK_one] at h
  simpa using h

theorem norm_lt_one_iff_vK_of_pos (he : 0 < eK p K) (x : Kˣ) :
    ‖((x : K) : PadicAlgCl p)‖ < 1 ↔ 1 ≤ vK p K x := by
  have h := norm_le_norm_iff_vK_of_pos p K he 1 x
  rw [vK_one] at h
  have h' : (1 : ℝ) ≤ ‖((x : K) : PadicAlgCl p)‖ ↔ vK p K x ≤ 0 := by simpa using h
  rw [← not_le, h']
  omega

theorem norm_eq_rpow_vK (hK : FiniteDimensional ℚ_[p] K) (x : Kˣ) :
    ‖((x : K) : PadicAlgCl p)‖ = (p : ℝ) ^ (- (vK p K x : ℝ) / eK p K) :=
  norm_eq_rpow_vK_of_pos p K (eK_pos p K hK) x

theorem norm_le_one_iff_vK (hK : FiniteDimensional ℚ_[p] K) (x : Kˣ) :
    ‖((x : K) : PadicAlgCl p)‖ ≤ 1 ↔ 0 ≤ vK p K x := norm_le_one_iff_vK_of_pos p K (eK_pos p K hK) x

theorem norm_lt_one_iff_vK (hK : FiniteDimensional ℚ_[p] K) (x : Kˣ) :
    ‖((x : K) : PadicAlgCl p)‖ < 1 ↔ 1 ≤ vK p K x := norm_lt_one_iff_vK_of_pos p K (eK_pos p K hK) x

theorem norm_le_norm_iff_vK (hK : FiniteDimensional ℚ_[p] K) (x y : Kˣ) :
    ‖((x : K) : PadicAlgCl p)‖ ≤ ‖((y : K) : PadicAlgCl p)‖ ↔ vK p K y ≤ vK p K x :=
  norm_le_norm_iff_vK_of_pos p K (eK_pos p K hK) x y

theorem vK_p (x : Kˣ) (hx : ((x : K) : PadicAlgCl p) = (p : PadicAlgCl p)) : vK p K x = eK p K := by
  apply Int.cast_injective (α := ℝ)
  rw [vK_spec, hx, logb_norm_p]
  simp

variable {K L}

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
