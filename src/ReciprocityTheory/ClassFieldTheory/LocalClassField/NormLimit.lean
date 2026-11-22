module

public import Mathlib
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecPairDefs
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.PairKEqZeroOfMemNormGrp
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.RestrictedMultiplicativeH1Subsingleton

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function
open scoped commutatorElement

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

section grp

variable {G : Type*} [Group G] (H : Subgroup G) [H.Normal] (hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (s : G)


end grp

end ReciprocityTheory.DiscreteGroups.LocalClassField
