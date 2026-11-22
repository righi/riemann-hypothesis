import Mathlib

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand

open Function

variable {M : Type*} [AddCommGroup M]

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    {DA NA : A →+ A} {DB NB : B →+ B} {DC NC : C →+ C} {f : A →+ B} {g : B →+ C}

@[simp] theorem kerMap_coe (f : A →+ B) (fD : ∀ a, f (DA a) = DB (f a)) (a : DA.ker) :
    ((kerMap f fD a : DB.ker) : B) = f a := rfl

@[simp] theorem Tmap_mk (f : A →+ B) (fD : ∀ a, f (DA a) = DB (f a)) (fN : ∀ a, f (NA a) = NB (f a))
    (a : DA.ker) : Tmap f fD fN (QuotientAddGroup.mk a) = QuotientAddGroup.mk (kerMap f fD a) := rfl

end ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
