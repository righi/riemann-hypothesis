module

public import Mathlib
public import ReciprocityTheory.GroupCohomology.InfRes
public import ReciprocityTheory.GroupCohomology.ComapZeroCoboundariesEqBot
public import ReciprocityTheory.GroupCohomology.PartialProdCoe

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2

section Alg

variable {R : Type*} [CommRing R] {G : Type*} [Group G] {A : Type*} [AddCommGroup A] [Module R A]
  (ρ : Representation R G A) (N : Subgroup G)

def IsTwoCocycle (c : G → G → A) : Prop := ∀ g h k, ρ g (c h k) - c (g * h) k + c g (h * k) - c g h = 0

variable {ρ}

variable {N} {c : G → G → A} (hc : IsTwoCocycle ρ c)
  {r s : G → G} (hrs : ∀ g, r g * s g = g) (hr : ∀ g, r g ∈ N)
  (hrn : ∀ n ∈ N, ∀ g, r (n * g) = n * r g) (hsn : ∀ n ∈ N, ∀ g, s (n * g) = s g)

end Alg

end ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
