module

public import Mathlib
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecDefs
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.QZDefs
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Brauer

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh

noncomputable section

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
