import Mathlib

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt

open Finset

variable {R : Type*} [Field R] (G : Type*) [Group G] [Fintype G] [MulSemiringAction G R]

namespace Filt

variable {G} {I : ℕ → AddSubgroup R} {e : R →+ R} (h : Filt G I e)

include h

theorem mem_V {n : ℕ} {u : Rˣ} : u ∈ h.V n ↔ (u : R) - 1 ∈ I n := Iff.rfl

theorem mkU_val (x : R) (hx : x ∈ I 0) : (h.mkU x hx : R) = 1 + x := rfl

end Filt

end ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt
