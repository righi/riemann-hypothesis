module

public import Mathlib

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand

open Function

variable {M : Type*} [AddCommGroup M]

abbrev T (D N : M →+ M) : Type _ := D.ker ⧸ (N.range.addSubgroupOf D.ker)

noncomputable def q (D N : M →+ M) : ℚ := (Nat.card (T D N) : ℚ) / (Nat.card (T N D) : ℚ)

structure SES {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (DA NA : A →+ A) (DB NB : B →+ B) (DC NC : C →+ C) (f : A →+ B) (g : B →+ C) : Prop where
  inj : Injective f
  exact : Function.Exact f g
  surj : Surjective g
  fD : ∀ a, f (DA a) = DB (f a)
  fN : ∀ a, f (NA a) = NB (f a)
  gD : ∀ b, g (DB b) = DC (g b)
  gN : ∀ b, g (NB b) = NC (g b)
  DN : ∀ b, DB (NB b) = 0
  ND : ∀ b, NB (DB b) = 0

theorem mk_eq_zero_iff {D N : M →+ M} (x : D.ker) :
    (QuotientAddGroup.mk x : T D N) = 0 ↔ (x : M) ∈ N.range := by
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]

theorem mk_eq_mk_iff {D N : M →+ M} (x y : D.ker) :
    (QuotientAddGroup.mk x : T D N) = QuotientAddGroup.mk y ↔ (x : M) - y ∈ N.range := by
  rw [← sub_eq_zero, ← QuotientAddGroup.mk_sub, mk_eq_zero_iff]; rfl

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    {DA NA : A →+ A} {DB NB : B →+ B} {DC NC : C →+ C} {f : A →+ B} {g : B →+ C}

def kerMap (f : A →+ B) (fD : ∀ a, f (DA a) = DB (f a)) : DA.ker →+ DB.ker :=
  (f.comp DA.ker.subtype).codRestrict DB.ker (fun a => by
    have ha : DA (a : A) = 0 := a.2
    rw [AddMonoidHom.mem_ker]
    change DB (f a) = 0
    rw [← fD, ha, map_zero])

def Tmap (f : A →+ B) (fD : ∀ a, f (DA a) = DB (f a)) (fN : ∀ a, f (NA a) = NB (f a)) :
    T DA NA →+ T DB NB :=
  QuotientAddGroup.map _ _ (kerMap f fD) (by
    intro a ha
    rw [AddSubgroup.mem_addSubgroupOf] at ha
    obtain ⟨x, hx⟩ := ha
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
    exact ⟨f x, by rw [← fN, hx]; rfl⟩)

theorem SES.swap (h : SES DA NA DB NB DC NC f g) : SES NA DA NB DB NC DC f g :=
  ⟨h.inj, h.exact, h.surj, h.fN, h.fD, h.gN, h.gD, h.ND, h.DN⟩

def Rel (DB : B →+ B) (f : A →+ B) (g : B →+ C) (c : C) (a : A) : Prop := ∃ b, g b = c ∧ f a = DB b

theorem exists_rel (h : SES DA NA DB NB DC NC f g) (c : DC.ker) : ∃ a : NA.ker, Rel DB f g c a := by
  obtain ⟨b, hb⟩ := h.surj c
  have hc : DC (c : C) = 0 := c.2
  have h1 : g (DB b) = 0 := by rw [h.gD, hb, hc]
  obtain ⟨a, ha⟩ := (h.exact _).1 h1
  exact ⟨⟨a, h.inj (by rw [h.fN, ha, h.ND, map_zero])⟩, b, hb, ha⟩

theorem rel_unique (h : SES DA NA DB NB DC NC f g) {c : C} {a a' : NA.ker} (h1 : Rel DB f g c a)
    (h2 : Rel DB f g c a') : (QuotientAddGroup.mk a : T NA DA) = QuotientAddGroup.mk a' := by
  obtain ⟨b, hb, ha⟩ := h1
  obtain ⟨b', hb', ha'⟩ := h2
  rw [mk_eq_mk_iff]
  obtain ⟨x, hx⟩ := (h.exact (b - b')).1 (by rw [map_sub, hb, hb', sub_self])
  exact ⟨x, h.inj (by rw [h.fD, hx, map_sub, map_sub, ha, ha'])⟩

theorem exists_delta (h : SES DA NA DB NB DC NC f g) :
    ∃ δ : T DC NC →+ T NA DA, ∀ (c : DC.ker) (a : NA.ker), Rel DB f g c a →
      δ (QuotientAddGroup.mk c) = QuotientAddGroup.mk a := by
  classical
  let δ0 : DC.ker →+ T NA DA := AddMonoidHom.mk'
    (fun c => QuotientAddGroup.mk (Classical.choose (exists_rel h c))) (fun c c' => by
      rw [← QuotientAddGroup.mk_add]
      refine rel_unique h (Classical.choose_spec (exists_rel h (c + c'))) ?_
      obtain ⟨b, hb, ha⟩ := Classical.choose_spec (exists_rel h c)
      obtain ⟨b', hb', ha'⟩ := Classical.choose_spec (exists_rel h c')
      exact ⟨b + b', by rw [map_add (f := _), hb, hb']; rfl, by
        rw [map_add (f := _), ← ha, ← ha', ← map_add (f := _)]; rfl⟩)
  have hδ0 : ∀ (c : DC.ker) (a : NA.ker), Rel DB f g c a → δ0 c = QuotientAddGroup.mk a :=
    fun c a hca => rel_unique h (Classical.choose_spec (exists_rel h c)) hca
  refine ⟨QuotientAddGroup.lift _ δ0 ?_, fun c a hca => ?_⟩
  · intro c hc
    rw [AddSubgroup.mem_addSubgroupOf] at hc
    obtain ⟨c0, hc0⟩ := hc
    obtain ⟨b0, rfl⟩ := h.surj c0
    rw [AddMonoidHom.mem_ker, hδ0 c 0 ⟨NB b0, by rw [h.gN, hc0], by rw [h.DN]; exact map_zero f⟩]
    rfl
  · rw [QuotientAddGroup.lift_mk]
    exact hδ0 c a hca

section Count

variable {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]

end Count

end ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
