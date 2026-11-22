import ReciprocityTheory.ClassFieldTheory.LocalClassField.HerbrandA

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand

open Function

section Cyclic

variable {k G M : Type*} [CommRing k] [Group G] [Fintype G] [AddCommGroup M] [Module k M]

@[simp] theorem dHom_apply (ρ : Representation k G M) (g : G) (x : M) : dHom ρ g x = ρ g x - x := rfl

theorem h_eq (ρ : Representation k G M) (g : G) :
    h ρ g = (Nat.card (TateZerothCohomology ρ g) : ℚ) / (Nat.card (H1 ρ g) : ℚ) := rfl

variable {A B C : Type*} [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
  [AddCommGroup C] [Module k C]

end Cyclic

end ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
