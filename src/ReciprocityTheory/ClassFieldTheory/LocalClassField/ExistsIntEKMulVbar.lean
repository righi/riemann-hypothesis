import Mathlib
import ReciprocityTheory.NeutralLocalFields.Duality
import ReciprocityTheory.GroupCohomology.InfRes
import ReciprocityTheory.GroupCohomology.CardLenStatement
import ReciprocityTheory.ClassFieldTheory.LocalClassField.KbarRepContAction
import ReciprocityTheory.ClassFieldTheory.LocalClassField.HerbrandB
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrDefs
import ReciprocityTheory.ClassFieldTheory.LocalClassField.QZDefs

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh

noncomputable section

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

def fK : ℕ := Nat.log p (qK p K)

def vbar : KbarMult p →+ ℝ where
  toFun x := - Real.logb p ‖((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p)‖
  map_zero' := by
    show - Real.logb p ‖((1 : (PadicAlgCl p)ˣ) : PadicAlgCl p)‖ = 0
    simp
  map_add' x y := by
    show - Real.logb p ‖((Additive.toMul x * Additive.toMul y : (PadicAlgCl p)ˣ) : PadicAlgCl p)‖ = _
    rw [Units.val_mul, norm_mul, Real.logb_mul (norm_ne_zero_iff.2 (Units.ne_zero _))
      (norm_ne_zero_iff.2 (Units.ne_zero _))]
    ring

theorem vbar_apply (x : KbarMult p) :
    vbar p x = - Real.logb p ‖((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p)‖ := rfl

def multOf : AddSubgroup (KbarMult p) where
  carrier := {x | ((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p) ∈ K}
  zero_mem' := K.one_mem
  add_mem' := fun {x y} hx hy => K.mul_mem hx hy
  neg_mem' := fun {x} hx => by
    show (((Additive.toMul x : (PadicAlgCl p)ˣ)⁻¹ : (PadicAlgCl p)ˣ) : PadicAlgCl p) ∈ K
    rw [Units.val_inv_eq_inv_val]
    exact K.inv_mem hx

def ofK : Additive Kˣ →+ KbarMult p :=
  MonoidHom.toAdditive (Units.map (algebraMap K (PadicAlgCl p) : K →* PadicAlgCl p))

theorem ofK_mem (x : Additive Kˣ) : ofK p K x ∈ multOf p K := (Additive.toMul x : Kˣ).1.2

def valueGroup : AddSubgroup ℝ := (multOf p K).map (vbar p)

def eK : ℕ := (AddSubgroup.zmultiples (1 : ℝ)).relIndex (valueGroup p K)

theorem exists_int_eK_mul_vbar (x : KbarMult p) (hx : x ∈ multOf p K) :
    ∃ n : ℤ, (n : ℝ) = eK p K * vbar p x := by
  have h : eK p K • vbar p x ∈ AddSubgroup.zmultiples (1 : ℝ) :=
    AddSubgroup.nsmul_relIndex_mem _ (AddSubgroup.mem_map_of_mem _ hx)
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 h
  refine ⟨k, ?_⟩
  have hk' : (k : ℝ) = (eK p K) • vbar p x := by simpa using hk
  rw [hk', nsmul_eq_mul]

def vOnFun (x : multOf p K) : ℤ := (exists_int_eK_mul_vbar p K x.1 x.2).choose

theorem vOnFun_spec (x : multOf p K) : (vOnFun p K x : ℝ) = eK p K * vbar p x.1 :=
  (exists_int_eK_mul_vbar p K x.1 x.2).choose_spec

def vOn : multOf p K →+ ℤ where
  toFun := vOnFun p K
  map_zero' := by
    apply Int.cast_injective (α := ℝ)
    rw [vOnFun_spec]; simp
  map_add' x y := by
    apply Int.cast_injective (α := ℝ)
    rw [Int.cast_add, vOnFun_spec, vOnFun_spec, vOnFun_spec, AddSubgroup.coe_add, map_add, mul_add]

theorem vOn_spec (x : multOf p K) : (vOn p K x : ℝ) = eK p K * vbar p x.1 := vOnFun_spec p K x

def vK (x : Kˣ) : ℤ := vOn p K ⟨ofK p K (Additive.ofMul x), ofK_mem p K _⟩

theorem mem_Ubar_iff (x : KbarMult p) : x ∈ Ubar p ↔ vbar p x = 0 := Iff.rfl

def subG : Subgroup (GK p K) where
  carrier := {σ | ∀ x ∈ L, σ x = x}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {σ τ} hσ hτ x hx => by
    show σ (τ x) = x
    rw [hτ x hx, hσ x hx]
  inv_mem' := fun {σ} hσ x hx => by
    rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq]; exact (hσ x hx).symm

theorem mem_subG_iff (σ : GK p K) : σ ∈ subG p K L ↔ ∀ x ∈ L, σ x = x := Iff.rfl

def degLK : ℕ := (subG p K L).index

abbrev GalLK : Type := GK p K ⧸ subG p K L

variable {p K L} in
theorem resGK_apply (h : K ≤ L) (σ : GK p L) (x : PadicAlgCl p) : resGK h σ x = σ x := rfl

variable {p K L} in

theorem subG_normal_of_stable (h : ∀ (σ : GK p K), ∀ x ∈ L, σ x ∈ L) : (subG p K L).Normal := by
  refine ⟨fun n hn g x hx => ?_⟩
  show g (n (g⁻¹ x)) = x
  rw [hn _ (h g⁻¹ x hx)]
  show (g * g⁻¹) x = x
  rw [mul_inv_cancel]; rfl

theorem norm_map_GK (σ : GK p K) (x : PadicAlgCl p) : ‖σ x‖ = ‖x‖ :=
  (spectralNorm_eq_of_equiv (σ.restrictScalars ℚ_[p]) x).symm

def MaximalUnramifiedExtension : IntermediateField ℚ_[p] (PadicAlgCl p) := ⨆ n : ℕ, Kn p K (n + 1)

theorem Kn_stable (n : ℕ) (σ : GK p K) (x : PadicAlgCl p) (hx : x ∈ Kn p K n) : σ x ∈ Kn p K n := by
  have h : Kn p K n ≤ (Kn p K n).comap ((σ.restrictScalars ℚ_[p] : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
      PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p) := by
    refine sup_le (fun y hy => ?_) (IntermediateField.adjoin_le_iff.2 fun ζ hζ => ?_)
    · show σ y ∈ Kn p K n
      rw [show σ y = y from σ.commutes ⟨y, hy⟩]
      exact (le_sup_left : K ≤ Kn p K n) hy
    · show σ ζ ∈ Kn p K n
      refine (le_sup_right : _ ≤ Kn p K n) (IntermediateField.subset_adjoin _ _ ?_)
      show (σ ζ) ^ (qK p K ^ n - 1) = 1
      rw [← map_pow, show ζ ^ (qK p K ^ n - 1) = 1 from hζ, map_one]
  exact h hx

theorem Kur_stable (σ : GK p K) (x : PadicAlgCl p) (hx : x ∈ MaximalUnramifiedExtension p K) : σ x ∈ MaximalUnramifiedExtension p K := by
  have h : MaximalUnramifiedExtension p K ≤ (MaximalUnramifiedExtension p K).comap ((σ.restrictScalars ℚ_[p] : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
      PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p) :=
    iSup_le fun n y hy => (le_iSup (fun n : ℕ => Kn p K (n + 1)) n) (Kn_stable p K (n + 1) σ y hy)
  exact h hx

scoped instance subG_Kn_normal (n : ℕ) : (subG p K (Kn p K n)).Normal := subG_normal_of_stable (Kn_stable p K n)

scoped instance subG_Kur_normal : (subG p K (MaximalUnramifiedExtension p K)).Normal := subG_normal_of_stable (Kur_stable p K)

def IsFrob (σ : GK p K) : Prop := ∀ x : PadicAlgCl p, ‖x‖ ≤ 1 → ‖σ x - x ^ qK p K‖ < 1

def frobK : GK p K := Classical.epsilon (IsFrob p K)

def frobLK : GalLK p K L := QuotientGroup.mk (frobK p K)

scoped instance : TopologicalSpace (Ubar p) := instTopologicalSpaceSubtype

scoped instance : DiscreteTopology (Ubar p) := inferInstanceAs (DiscreteTopology ((Ubar p : Set (KbarMult p))))

scoped instance : IsTopologicalAddGroup (Ubar p) := inferInstance

scoped instance : DiscreteTopology (ubarT p K).V := inferInstanceAs (DiscreteTopology (Ubar p))

scoped instance [(subG p K L).Normal] : DiscreteTopology (layer p K L).V :=
  (InflationRestrictionInvariants.invariants_isInvRep (kbarT p K) (subG p K L)).2.1.discreteTopology

scoped instance [(subG p K L).Normal] : DiscreteTopology (layerU p K L).V :=
  (InflationRestrictionInvariants.invariants_isInvRep (ubarT p K) (subG p K L)).2.1.discreteTopology

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
