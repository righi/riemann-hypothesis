import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsD
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh

noncomputable section

variable (p : ℕ) [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem toLayer_val [(subG p K L).Normal] (x : multOf p L) : (toLayer p x : (layer p K L).V).1 = x.1 := rfl

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
