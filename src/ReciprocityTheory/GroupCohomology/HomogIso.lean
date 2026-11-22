module

public import ReciprocityTheory.GroupCohomology.CupConnRightStatement
public import ReciprocityTheory.GroupCohomology.HomogExistsStatement
public import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB

@[expose] public section

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

namespace HomogeneousCochainIso

theorem hgi_val {n : ℕ} (i : Fin (n + 3)) (j : Fin (n + 2)) :
    ((i.succAbove j : ℕ) + (j.predAbove i : ℕ) = i + j + 1) ∨
      ((i.succAbove j : ℕ) + (j.predAbove i : ℕ) + 1 = i + j) := by
  simp only [Fin.succAbove, Fin.predAbove, Fin.lt_def, Fin.val_castSucc, apply_dite Fin.val,
    Fin.val_pred, Fin.coe_castPred, dite_eq_ite, apply_ite Fin.val, Fin.val_succ]
  split_ifs <;> omega

theorem hgi_sign {n : ℕ} (i : Fin (n + 3)) (j : Fin (n + 2)) :
    (-1 : ℤ) ^ (i.succAbove j : ℕ) * (-1) ^ (j.predAbove i : ℕ) = -((-1) ^ (i : ℕ) * (-1) ^ (j : ℕ)) := by
  rw [← pow_add, ← pow_add]
  rcases hgi_val i j with h | h
  · rw [h, pow_succ]; ring
  · rw [← h, pow_succ]; ring

theorem hd_hd {V X : Type u} [AddCommGroup V] (n : ℕ) (F : (Fin (n + 1) → X) → V) :
    hd (n + 1) (hd n F) = 0 := by
  funext x
  simp only [hd, Finset.smul_sum, smul_smul, Pi.zero_apply]
  rw [← Finset.sum_product' (s := Finset.univ) (t := Finset.univ)
    (f := fun (i : Fin (n + 3)) (j : Fin (n + 2)) => ((-1 : ℤ) ^ (i : ℕ) * (-1) ^ (j : ℕ)) • F fun k => x (i.succAbove (j.succAbove k)))]
  refine Finset.sum_involution (fun p _ => (p.1.succAbove p.2, p.2.predAbove p.1)) ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ _
    simp only [Fin.succAbove_succAbove_succAbove_predAbove, hgi_sign, neg_smul]
    exact add_neg_cancel _
  · rintro ⟨i, j⟩ _ _ h
    simp only [Prod.mk.injEq] at h
    exact Fin.succAbove_ne i j h.1
  · intros; exact Finset.mem_univ _
  · rintro ⟨i, j⟩ _
    simp only [Fin.succAbove_succAbove_predAbove, Fin.predAbove_predAbove_succAbove]

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def hdL (R : Type u) [CommRing R] {V X : Type u} [AddCommGroup V] [Module R V] (n : ℕ) :
    ((Fin (n + 1) → X) → V) →ₗ[R] ((Fin (n + 2) → X) → V) where
  toFun := hd n
  map_add' F F' := by funext x; simp [hd, Finset.sum_add_distrib]
  map_smul' r F := by
    funext x
    simp only [hd, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

theorem hd_mem (M : TRep R G) (X : Type u) [TopologicalSpace X] [MulAction G X] (n : ℕ)
    (F : (Fin (n + 1) → X) → M.V) (hF : F ∈ hcoch M X n) : hd n F ∈ hcoch M X (n + 1) := by
  refine ⟨?_, fun g x => ?_⟩
  · exact continuous_finsetSum _ fun i _ => (continuous_const_smul ((-1 : ℤ) ^ (i : ℕ))).comp
      (hF.1.comp (continuous_pi fun j => continuous_apply (i.succAbove j)))
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [hd, hF.2, map_sum, map_zsmul]

def hcx (M : TRep R G) (X : Type u) [TopologicalSpace X] [MulAction G X] : Cx R where
  X n := hcoch M X n
  d n := (hdL R n).restrict fun F hF => hd_mem M X n F hF
  dd n F := Subtype.ext (hd_hd n F.1)

end HomogeneousCochainIso

open HomogeneousCochainIso

end

end ReciprocityTheory.Coh
