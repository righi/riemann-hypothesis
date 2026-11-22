module

public import Mathlib
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh

noncomputable section

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

structure IsAbLK : Prop where
  le : K ≤ L
  fin : FiniteDimensional ℚ_[p] L
  comm : commutator (GK p K) ≤ subG p K L

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
