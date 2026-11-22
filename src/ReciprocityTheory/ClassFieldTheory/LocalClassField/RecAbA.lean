module

public import Mathlib
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.QZDefs

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 Function

noncomputable section

section fin

variable (A : Type) [AddCommGroup A] [Finite A]

scoped instance : NeZero (Monoid.exponent (Multiplicative A)) := ⟨Monoid.exponent_ne_zero_of_finite⟩

variable {A}

end fin

section top

variable {G : Type} [Group G] [TopologicalSpace G] {A : Type} [AddCommGroup A] (π : Additive G →+ A)
  (hc : IsLocallyConstant fun g : G => π (Additive.ofMul g))

variable {π}

include hc

end top

section quot

variable {G : Type} [Group G] (H : Subgroup G) [H.Normal]

end quot

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
