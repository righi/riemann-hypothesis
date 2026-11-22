import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnitsHerbrandC

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable {p : ℕ} [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}

section

variable [(subG p K L).Normal]

theorem uval_add (a b : (layerU p K L).V) : uval (a + b) = uval a * uval b := rfl

theorem uval_rho (σ : GK p K) (w : (layerU p K L).V) :
    uval ((layerU p K L).rho (QuotientGroup.mk σ) w) = σ (uval w) := rfl

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
