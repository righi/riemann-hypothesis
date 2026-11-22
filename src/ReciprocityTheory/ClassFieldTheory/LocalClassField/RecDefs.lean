import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh

noncomputable section

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem mem_normGrp_iff (x : Kˣ) :
    x ∈ normGrp p K L ↔ ∃ y ∈ multOf p L, normHom p K L y = ofK p K (Additive.ofMul x) := Iff.rfl

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
