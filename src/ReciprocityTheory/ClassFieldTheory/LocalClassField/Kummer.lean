module

public import ReciprocityTheory.ClassFieldTheory.LocalClassField.KummerA
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.RestrictedMultiplicativeH1Subsingleton

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh

namespace Kummer

noncomputable section

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ) [NeZero n]

end

end Kummer

open Kummer

end ReciprocityTheory.DiscreteGroups.LocalClassField
