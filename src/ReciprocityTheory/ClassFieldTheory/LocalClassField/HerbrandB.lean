module

public import ReciprocityTheory.ClassFieldTheory.LocalClassField.HerbrandA

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand

open Function

section Abstract

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    {DA NA : A →+ A} {DB NB : B →+ B} {f : A →+ B}

end Abstract

section Cyclic

variable {k G M : Type*} [CommRing k] [Group G] [Fintype G] [AddCommGroup M] [Module k M]

def dHom (ρ : Representation k G M) (g : G) : M →+ M := (ρ g - 1 : Module.End k M).toAddMonoidHom

def nHom (ρ : Representation k G M) : M →+ M := (ρ.norm : Module.End k M).toAddMonoidHom

abbrev H1 (ρ : Representation k G M) (g : G) : Type _ := T (nHom ρ) (dHom ρ g)

noncomputable def h (ρ : Representation k G M) (g : G) : ℚ := q (dHom ρ g) (nHom ρ)

variable {A B C : Type*} [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
  [AddCommGroup C] [Module k C]

end Cyclic

end ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
