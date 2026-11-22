import Mathlib
import ReciprocityTheory.NeutralLocalFields.Reciprocity

noncomputable section

open NumberField IsDedekindDomain Representation

namespace Neutral.B1

section CohA

set_option linter.unusedVariables false

noncomputable section

open Representation

variable {R : Type*} [CommRing R]
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

section ContMaps

variable (R M)

def contMaps (X : Type*) [TopologicalSpace X] : Submodule R (X → M) where
  carrier := {f | Continuous f}
  zero_mem' := continuous_const
  add_mem' hf hg := hf.add hg
  smul_mem' c _ hf := hf.const_smul c

variable {R M}

theorem mem_contMaps {X : Type*} [TopologicalSpace X] (f : X → M) :
    f ∈ contMaps R M X ↔ Continuous f := Iff.rfl

end ContMaps

def ContAction (rho : Representation R G M) : Prop :=
  Continuous (fun p : G × M => rho p.1 p.2)

variable (rho : Representation R G M)

def H0 : Submodule R M := rho.invariants

theorem mem_riemannRochSpace_iff_regularAt_everywhere (m : M) : m ∈ H0 rho ↔ ∀ g, rho g m = m := Iff.rfl

def Z1 : Submodule R (G → M) where
  carrier := {f | Continuous f ∧ ∀ g h, f (g * h) = f g + rho g (f h)}
  zero_mem' := ⟨continuous_const, fun g h => by simp⟩
  add_mem' := fun {f f'} hf hf' => ⟨hf.1.add hf'.1, fun g h => by
    simp only [Pi.add_apply, hf.2, hf'.2, map_add]; abel⟩
  smul_mem' c f hf := ⟨hf.1.const_smul c, fun g h => by
    simp only [Pi.smul_apply, hf.2, map_smul, smul_add]⟩

theorem mem_Z1_iff_cocycle (f : G → M) :
    f ∈ Z1 rho ↔ Continuous f ∧ ∀ g h, f (g * h) = f g + rho g (f h) := Iff.rfl

def d0 : M →ₗ[R] (G → M) := LinearMap.pi fun g => rho g - LinearMap.id

@[simp] theorem amitsur_d0_apply (m : M) (g : G) : d0 rho m g = rho g m - m := rfl

def Bd1 : Submodule R (G → M) := LinearMap.range (d0 rho)

theorem mem_contCoboundaries1 (f : G → M) : f ∈ Bd1 rho ↔ ∃ m, ∀ g, f g = rho g m - m := by
  constructor
  · rintro ⟨m, rfl⟩; exact ⟨m, fun g => rfl⟩
  · rintro ⟨m, hm⟩; exact ⟨m, funext fun g => (hm g).symm⟩

abbrev H1 := Z1 rho ⧸ (Bd1 rho).comap (Z1 rho).subtype

def Z2 : Submodule R (G × G → M) where
  carrier := {f | Continuous f ∧
    ∀ g h k, rho g (f (h, k)) - f (g * h, k) + f (g, h * k) - f (g, h) = 0}
  zero_mem' := ⟨continuous_const, fun g h k => by simp⟩
  add_mem' := fun {f f'} hf hf' => ⟨hf.1.add hf'.1, fun g h k => by
    have e1 := hf.2 g h k; have e2 := hf'.2 g h k
    simp only [Pi.add_apply, map_add]
    calc _ = (rho g (f (h, k)) - f (g * h, k) + f (g, h * k) - f (g, h)) +
          (rho g (f' (h, k)) - f' (g * h, k) + f' (g, h * k) - f' (g, h)) := by abel
      _ = 0 := by rw [e1, e2, add_zero]⟩
  smul_mem' c f hf := ⟨hf.1.const_smul c, fun g h k => by
    have e := hf.2 g h k
    simp only [Pi.smul_apply, map_smul]
    rw [← smul_sub, ← smul_add, ← smul_sub, e, smul_zero]⟩

theorem mem_cocycles2 (f : G × G → M) :
    f ∈ Z2 rho ↔ Continuous f ∧
      ∀ g h k, rho g (f (h, k)) - f (g * h, k) + f (g, h * k) - f (g, h) = 0 := Iff.rfl

def d1 : (G → M) →ₗ[R] (G × G → M) where
  toFun c p := rho p.1 (c p.2) - c (p.1 * p.2) + c p.1
  map_add' c c' := by
    funext p; simp only [Pi.add_apply, map_add]; abel
  map_smul' r c := by
    funext p; simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_sub, smul_add]

@[simp] theorem d1_apply (c : G → M) (g h : G) :
    d1 rho c (g, h) = rho g (c h) - c (g * h) + c g := rfl

def Bd2 : Submodule R (G × G → M) := (contMaps R M G).map (d1 rho)

theorem mem_contCoboundaries2 (f : G × G → M) :
    f ∈ Bd2 rho ↔ ∃ c : G → M, Continuous c ∧ d1 rho c = f := Iff.rfl

abbrev H2 := Z2 rho ⧸ (Bd2 rho).comap (Z2 rho).subtype

def Cn (rho : Representation R G M) (n : ℕ) : Submodule R ((Fin n → G) → M) := contMaps R M (Fin n → G)

def dn (n : ℕ) : ((Fin n → G) → M) →ₗ[R] ((Fin (n + 1) → G) → M) where
  toFun f g := rho (g 0) (f fun i => g i.succ) + Finset.univ.sum fun j : Fin (n + 1) =>
    (-1 : R) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g)
  map_add' f f' := by
    funext g
    simp [Finset.sum_add_distrib, add_add_add_comm]
  map_smul' r f := by
    funext g
    simp [Finset.smul_sum, ← smul_assoc, mul_comm r]

theorem dn_apply (n : ℕ) (f : (Fin n → G) → M) (g : Fin (n + 1) → G) :
    dn rho n f g = rho (g 0) (f fun i => g i.succ) + Finset.univ.sum fun j : Fin (n + 1) =>
      (-1 : R) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g) := rfl

def Zn (n : ℕ) : Submodule R ((Fin n → G) → M) := Cn rho n ⊓ LinearMap.ker (dn rho n)

def Bn : (n : ℕ) → Submodule R ((Fin n → G) → M)
  | 0 => ⊥
  | n + 1 => (Cn rho n).map (dn rho n)

abbrev Hn (n : ℕ) := Zn rho n ⧸ (Bn rho n).comap (Zn rho n).subtype

section Restriction

variable {H : Type*} [Group H] [TopologicalSpace H] (phi : H →* G)

variable (hphi : Continuous phi)
include hphi

def restrictCocycles1 : Z1 rho →ₗ[R] Z1 (rho.comp phi) where
  toFun f := ⟨f.1 ∘ phi, f.2.1.comp hphi, fun g h => by
    simp only [Function.comp_apply, map_mul, MonoidHom.coe_comp]
    exact f.2.2 _ _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem restrictCocycles1_apply (f : Z1 rho) (h : H) : (restrictCocycles1 rho phi hphi f).1 h = f.1 (phi h) := rfl

def resH1 : H1 rho →ₗ[R] H1 (rho.comp phi) :=
  Submodule.mapQ _ _ (restrictCocycles1 rho phi hphi) fun f hf => by
    obtain ⟨m, hm⟩ := (mem_contCoboundaries1 rho _).1 hf
    exact (mem_contCoboundaries1 _ _).2 ⟨m, fun h => hm (phi h)⟩

def restrictCocycles2 : Z2 rho →ₗ[R] Z2 (rho.comp phi) where
  toFun f := ⟨fun p => f.1 (phi p.1, phi p.2), f.2.1.comp (hphi.prodMap hphi), fun g h k => by
    simp only [map_mul, MonoidHom.coe_comp, Function.comp_apply]
    exact f.2.2 _ _ _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem restrictCocycles2_apply (f : Z2 rho) (g h : H) :
    (restrictCocycles2 rho phi hphi f).1 (g, h) = f.1 (phi g, phi h) := rfl

def resH2 : H2 rho →ₗ[R] H2 (rho.comp phi) :=
  Submodule.mapQ _ _ (restrictCocycles2 rho phi hphi) fun f hf => by
    obtain ⟨c, hc, hcf⟩ := (mem_contCoboundaries2 rho _).1 hf
    refine (mem_contCoboundaries2 _ _).2 ⟨c ∘ phi, hc.comp hphi, ?_⟩
    funext p
    have e := congrFun hcf (phi p.1, phi p.2)
    simp only [Submodule.coe_subtype] at e
    change _ = f.1 (phi p.1, phi p.2)
    rw [← e]
    simp [d1]

end Restriction

section Pair

variable {G' : Type*} [Group G'] [TopologicalSpace G']
  {M' : Type*} [AddCommGroup M'] [Module R M'] [TopologicalSpace M']
  [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
  (rho' : Representation R G' M') (phi : G' →* G) (hphi : Continuous phi)
  (u : M →ₗ[R] M') (hu : Continuous u) (hcompat : ∀ g m, u (rho (phi g) m) = rho' g (u m))
include hphi hu hcompat

def compatiblePairCocycles1 : Z1 rho →ₗ[R] Z1 rho' where
  toFun f := ⟨fun g => u (f.1 (phi g)), hu.comp (f.2.1.comp hphi), fun g h => by
    simp only [map_mul, f.2.2, map_add, hcompat]⟩
  map_add' f f' := Subtype.ext (funext fun g => map_add u _ _)
  map_smul' r f := Subtype.ext (funext fun g => map_smul u _ _)

@[simp] theorem compatiblePairCocycles1_apply (f : Z1 rho) (g : G') :
    (compatiblePairCocycles1 rho rho' phi hphi u hu hcompat f).1 g = u (f.1 (phi g)) := rfl

def compatiblePairCocycles2 : Z2 rho →ₗ[R] Z2 rho' where
  toFun f := ⟨fun p => u (f.1 (phi p.1, phi p.2)), hu.comp (f.2.1.comp (hphi.prodMap hphi)),
    fun g h k => by
      have e := congrArg u (f.2.2 (phi g) (phi h) (phi k))
      simp only [map_sub, map_add, map_zero, hcompat] at e
      simpa only [map_mul] using e⟩
  map_add' f f' := Subtype.ext (funext fun g => map_add u _ _)
  map_smul' r f := Subtype.ext (funext fun g => map_smul u _ _)

@[simp] theorem compatiblePairCocycles2_apply (f : Z2 rho) (g h : G') :
    (compatiblePairCocycles2 rho rho' phi hphi u hu hcompat f).1 (g, h) = u (f.1 (phi g, phi h)) := rfl

end Pair

section RestrictionN

variable {H : Type*} [Group H] [TopologicalSpace H] (phi : H →* G)

theorem contractNth_map {n : ℕ} (j : Fin (n + 1)) (g : Fin (n + 1) → H) :
    (fun k => phi (Fin.contractNth j (· * ·) g k)) =
      Fin.contractNth j (· * ·) (fun k => phi (g k)) := by
  funext k
  rcases lt_trichotomy (k : ℕ) j with h | h | h
  · simp only [Fin.contractNth_apply_of_lt _ _ _ _ h]
  · simp only [Fin.contractNth_apply_of_eq _ _ _ _ h, map_mul]
  · simp only [Fin.contractNth_apply_of_gt _ _ _ _ h]

theorem dn_comp (n : ℕ) (f : (Fin n → G) → M) (g : Fin (n + 1) → H) :
    dn (rho.comp phi) n (fun x => f fun i => phi (x i)) g = dn rho n f (fun i => phi (g i)) := by
  simp only [dn_apply, MonoidHom.coe_comp, Function.comp_apply]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [contractNth_map]

variable (hphi : Continuous phi)
include hphi

theorem continuous_comp_tuple (n : ℕ) {f : (Fin n → G) → M} (hf : Continuous f) :
    Continuous (fun x : Fin n → H => f fun i => phi (x i)) :=
  hf.comp (continuous_pi fun i => hphi.comp (continuous_apply i))

def resZn (n : ℕ) : Zn rho n →ₗ[R] Zn (rho.comp phi) n where
  toFun f := ⟨fun x => f.1 fun i => phi (x i), by
    obtain ⟨hc, hk⟩ := Submodule.mem_inf.1 f.2
    refine Submodule.mem_inf.2 ⟨continuous_comp_tuple phi hphi n hc, LinearMap.mem_ker.2 ?_⟩
    funext g
    rw [dn_comp]
    exact congrFun (LinearMap.mem_ker.1 hk) _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem resZn_apply (n : ℕ) (f : Zn rho n) (x : Fin n → H) :
    (resZn rho phi hphi n f).1 x = f.1 fun i => phi (x i) := rfl

end RestrictionN

end

end CohA

section Coh

noncomputable section

open Representation

variable {R : Type*} [CommRing R]
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

variable (rho : Representation R G M)

section Cup

variable {M' : Type*} [AddCommGroup M'] [Module R M'] [TopologicalSpace M']
  [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
  {P : Type*} [AddCommGroup P] [Module R P] [TopologicalSpace P]
  [IsTopologicalAddGroup P] [ContinuousConstSMul R P]
  (rho' : Representation R G M') (rhoP : Representation R G P)
  (b : M →ₗ[R] M' →ₗ[R] P) (hb : Continuous fun p : M × M' => b p.1 p.2)
  (hbe : ∀ g x y, b (rho g x) (rho' g y) = rhoP g (b x y))

section CupZ11

include hb hbe

def cupCocycleZ1Z1 (hrho' : ContAction rho') : Z1 rho →ₗ[R] Z1 rho' →ₗ[R] Z2 rhoP :=
  LinearMap.mk₂ R
    (fun x y => ⟨fun p => b (x.1 p.1) (rho' p.1 (y.1 p.2)),
      hb.comp ((x.2.1.comp continuous_fst).prodMk
        (hrho'.comp (continuous_fst.prodMk (y.2.1.comp continuous_snd)))),
      fun g h k => by
        have hx := x.2.2 g h
        have hy := y.2.2 h k
        dsimp only
        rw [← hbe, hx, hy, map_mul, Module.End.mul_apply]
        simp only [map_add, LinearMap.add_apply]
        abel⟩)
    (fun x x' y => Subtype.ext (funext fun p => by simp))
    (fun r x y => Subtype.ext (funext fun p => by simp))
    (fun x y y' => Subtype.ext (funext fun p => by simp))
    (fun r x y => Subtype.ext (funext fun p => by simp))

@[simp] theorem cupCocycleZ1Z1_apply (hrho' : ContAction rho') (x : Z1 rho) (y : Z1 rho') (g h : G) :
    (cupCocycleZ1Z1 rho rho' rhoP b hb hbe hrho' x y).1 (g, h) = b (x.1 g) (rho' g (y.1 h)) := rfl

end CupZ11

include hb hbe

def cupCocycleH0Z2 : H0 rho →ₗ[R] Z2 rho' →ₗ[R] Z2 rhoP :=
  LinearMap.mk₂ R
    (fun m f => ⟨fun p => b m.1 (f.1 p), hb.comp (continuous_const.prodMk f.2.1),
      fun g h k => by
        have e := congrArg (b m.1) (f.2.2 g h k)
        simp only [map_sub, map_add, map_zero] at e
        rw [← hbe, (mem_riemannRochSpace_iff_regularAt_everywhere rho m.1).1 m.2 g]
        exact e⟩)
    (fun m m' f => Subtype.ext (funext fun p => by simp))
    (fun r m f => Subtype.ext (funext fun p => by simp))
    (fun m f f' => Subtype.ext (funext fun p => by simp))
    (fun r m f => Subtype.ext (funext fun p => by simp))

@[simp] theorem cupCocycleH0Z2_apply (m : H0 rho) (f : Z2 rho') (p : G × G) :
    (cupCocycleH0Z2 rho rho' rhoP b hb hbe m f).1 p = b m.1 (f.1 p) := rfl

def cupCocycleZ2H0 : Z2 rho →ₗ[R] H0 rho' →ₗ[R] Z2 rhoP :=
  LinearMap.mk₂ R
    (fun f m => ⟨fun p => b (f.1 p) m.1, hb.comp (f.2.1.prodMk continuous_const),
      fun g h k => by
        have e := congrArg (b.flip m.1) (f.2.2 g h k)
        simp only [map_sub, map_add, map_zero, LinearMap.flip_apply] at e
        rw [← (mem_riemannRochSpace_iff_regularAt_everywhere rho' m.1).1 m.2 g, hbe, (mem_riemannRochSpace_iff_regularAt_everywhere rho' m.1).1 m.2 g] at e
        exact e⟩)
    (fun f f' m => Subtype.ext (funext fun p => by simp))
    (fun r f m => Subtype.ext (funext fun p => by simp))
    (fun f m m' => Subtype.ext (funext fun p => by simp))
    (fun r f m => Subtype.ext (funext fun p => by simp))

@[simp] theorem cupCocycleZ2H0_apply (f : Z2 rho) (m : H0 rho') (p : G × G) :
    (cupCocycleZ2H0 rho rho' rhoP b hb hbe f m).1 p = b (f.1 p) m.1 := rfl

end Cup

section Inertia

variable {D : Type*} [Group D] [TopologicalSpace D] (rhoD : Representation R D M)
  (J : Subgroup D)

def H1ur : Submodule R (H1 rhoD) :=
  LinearMap.ker (resH1 rhoD J.subtype continuous_subtype_val)

end Inertia

end

end Coh

instance (priority := 100) continuousConstSMul_of_discrete {R M : Type*} [SMul R M]
    [TopologicalSpace M] [DiscreteTopology M] : ContinuousConstSMul R M :=
  ⟨fun _ => continuous_of_discreteTopology⟩

section Coeff

variable {R : Type*} [CommRing R] {Γ : Type*} [Group Γ]
  {M : Type*} [AddCommGroup M] [Module R M]

@[simp] theorem charRep_apply (χ : Γ →* Rˣ) (g : Γ) (x : R) :
    charRep χ g x = ((χ g : Rˣ) : R) * x := rfl

variable (R M) in

def TDual := Module.Dual R M

instance : AddCommGroup (TDual R M) := inferInstanceAs (AddCommGroup (Module.Dual R M))
instance : Module R (TDual R M) := inferInstanceAs (Module R (Module.Dual R M))
instance : TopologicalSpace (TDual R M) := ⊥
instance : DiscreteTopology (TDual R M) := ⟨rfl⟩
instance : FunLike (TDual R M) M R := inferInstanceAs (FunLike (M →ₗ[R] R) M R)

def TDual.mk (φ : M →ₗ[R] R) : TDual R M := φ

@[simp] theorem TDual.mk_apply (φ : M →ₗ[R] R) (m : M) : TDual.mk φ m = φ m := rfl

@[simp] theorem TDual.add_apply (φ ψ : TDual R M) (m : M) : (φ + ψ) m = φ m + ψ m := rfl

@[simp] theorem TDual.smul_apply (c : R) (φ : TDual R M) (m : M) : (c • φ) m = c * φ m := rfl

@[ext] theorem TDual.ext {φ ψ : TDual R M} (h : ∀ m, φ m = ψ m) : φ = ψ := LinearMap.ext h

def twDual (χ : Γ →* Rˣ) (rho : Representation R Γ M) : Representation R Γ (TDual R M) where
  toFun g :=
    { toFun := fun φ => TDual.mk (((χ g : Rˣ) : R) • ((φ : M →ₗ[R] R) ∘ₗ rho g⁻¹))
      map_add' := fun φ ψ => by
        ext m
        show ((χ g : Rˣ) : R) * (φ (rho g⁻¹ m) + ψ (rho g⁻¹ m)) =
          ((χ g : Rˣ) : R) * φ (rho g⁻¹ m) + ((χ g : Rˣ) : R) * ψ (rho g⁻¹ m)
        ring
      map_smul' := fun c φ => by
        ext m
        show ((χ g : Rˣ) : R) * (c * φ (rho g⁻¹ m)) = c * (((χ g : Rˣ) : R) * φ (rho g⁻¹ m))
        ring }
  map_one' := by ext φ m; simp; rfl
  map_mul' g h := by
    ext φ m
    show _ * φ (rho (g * h)⁻¹ m) = _ * (_ * φ (rho h⁻¹ (rho g⁻¹ m)))
    rw [mul_inv_rev, map_mul rho, Module.End.mul_apply, map_mul χ, Units.val_mul, mul_assoc]

@[simp] theorem twDual_apply (χ : Γ →* Rˣ) (rho : Representation R Γ M) (g : Γ) (φ : TDual R M)
    (m : M) : twDual χ rho g φ m = ((χ g : Rˣ) : R) * φ (rho g⁻¹ m) := rfl

def evalPair : M →ₗ[R] TDual R M →ₗ[R] R := LinearMap.applyₗ

@[simp] theorem evalPair_apply (m : M) (φ : TDual R M) : evalPair m φ = φ m := rfl

def tdualMap {M' : Type*} [AddCommGroup M'] [Module R M'] (u : M →ₗ[R] M') :
    TDual R M' →ₗ[R] TDual R M :=
  u.dualMap

@[simp] theorem tdualMap_apply {M' : Type*} [AddCommGroup M'] [Module R M'] (u : M →ₗ[R] M')
    (φ : TDual R M') (m : M) : tdualMap u φ m = φ (u m) := rfl

end Coeff

section Cup

variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {Γ : Type*} [Group Γ] {M : Type*} [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [DiscreteTopology M]

theorem ContAction.comp' [TopologicalSpace Γ] {D : Type*} [Group D] [TopologicalSpace D]
    {rho : Representation R Γ M} (h : ContAction rho) {φ : D →* Γ} (hφ : Continuous φ) :
    ContAction (rho.comp φ) :=
  h.comp ((hφ.comp continuous_fst).prodMk continuous_snd)

variable {D : Type*} [Group D] [TopologicalSpace D]
  (χ : Γ →* Rˣ) (rho : Representation R Γ M) (φ : D →* Γ)

end Cup

section Local

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

abbrev GK : Type := PadicAlgCl p ≃ₐ[K] PadicAlgCl p

def inertiaSet : Set (GK p K) := {σ | ∀ x : PadicAlgCl p, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1}

def inertiaK : Subgroup (GK p K) := Subgroup.closure (inertiaSet p K)

variable {p K}

variable (p) in

def KbarMult : Type := Additive (PadicAlgCl p)ˣ

instance : AddCommGroup (KbarMult p) := inferInstanceAs (AddCommGroup (Additive (PadicAlgCl p)ˣ))
instance : TopologicalSpace (KbarMult p) := ⊥
instance : DiscreteTopology (KbarMult p) := ⟨rfl⟩

end Local

def LocalCohomologyFinite : Prop := ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)),
  FiniteDimensional ℚ_[p] K → ∀ (n : ℕ) [NeZero n] (M : Type) [AddCommGroup M]
  [Module (ZMod n) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
  (rho : Representation (ZMod n) (GK p K) M), ContAction rho →
    Finite (H0 rho) ∧ Finite (H1 rho) ∧ Finite (H2 rho) ∧ ∀ i, 3 ≤ i → Subsingleton (Hn rho i)

def LocalInvariantIsomorphism : Prop := ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)),
  FiniteDimensional ℚ_[p] K →
    Nonempty (H2 (kbarRep p K) ≃ₗ[ℤ] QZ) ∧
    ∀ (n : ℕ) [NeZero n], Nonempty (H2 (charRep (cycK p K n)) ≃ₗ[ZMod n] ZMod n)

section Global

abbrev G (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω] := Ω ≃ₐ[F] Ω

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

def IsPlaceOver (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ x : 𝓞 F, A.valuation (algebraMap F Ω (x : F)) < 1 ↔ x ∈ v.asIdeal

variable (F) in

abbrev Dec (A : ValuationSubring Ω) : Subgroup (G F Ω) := A.decompositionSubgroup F

def Inertia (A : ValuationSubring Ω) : Set (G F Ω) :=
  {σ | σ ∈ Dec F A ∧ ∀ x, A.valuation x ≤ 1 → A.valuation (σ x - x) < 1}

variable (F) in

def DecInf (j : Ω →+* ℂ) : Subgroup (G F Ω) where
  carrier := {σ | (∀ x, j (σ x) = j x) ∨ ∀ x, j (σ x) = starRingEnd ℂ (j x)}
  one_mem' := Or.inl fun x => rfl
  mul_mem' := by
    rintro σ τ (hσ | hσ) (hτ | hτ)
    · exact Or.inl fun x => by simp only [AlgEquiv.mul_apply, hσ, hτ]
    · exact Or.inr fun x => by simp only [AlgEquiv.mul_apply, hσ, hτ]
    · exact Or.inr fun x => by simp only [AlgEquiv.mul_apply, hσ, hτ]
    · exact Or.inl fun x => by simp only [AlgEquiv.mul_apply, hσ, hτ, Complex.conj_conj]
  inv_mem' := by
    rintro σ (hσ | hσ)
    · refine Or.inl fun x => ?_
      have := hσ (σ⁻¹ x)
      rw [show σ (σ⁻¹ x) = x from by simp] at this
      exact this.symm
    · refine Or.inr fun x => ?_
      have := hσ (σ⁻¹ x)
      rw [show σ (σ⁻¹ x) = x from by simp] at this
      rw [this, Complex.conj_conj]

theorem mem_DecInf (j : Ω →+* ℂ) (σ : G F Ω) :
    σ ∈ DecInf F j ↔ (∀ x, j (σ x) = j x) ∨ ∀ x, j (σ x) = starRingEnd ℂ (j x) := Iff.rfl

instance finite_DecInf (j : Ω →+* ℂ) : Finite (DecInf F j) := by
  classical
  refine Finite.of_injective (fun σ : DecInf F j => decide (∀ x, j (σ.1 x) = j x)) ?_
  intro σ τ h
  have hiff : (∀ x, j (σ.1 x) = j x) ↔ ∀ x, j (τ.1 x) = j x := by simpa using h
  have hσ := (mem_DecInf j σ.1).1 σ.2
  have hτ := (mem_DecInf j τ.1).1 τ.2
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  apply j.injective
  by_cases h1 : ∀ x, j (σ.1 x) = j x
  · rw [h1 x, hiff.1 h1 x]
  · have h2 : ¬ ∀ x, j (τ.1 x) = j x := fun h' => h1 (hiff.2 h')
    rw [hσ.resolve_left h1 x, hτ.resolve_left h2 x]

section unram

variable (S : Set (HeightOneSpectrum (𝓞 F)))

variable (Ω) in

def NS : Subgroup (G F Ω) :=
  (Subgroup.normalClosure
    (⋃ v ∈ Sᶜ, ⋃ A ∈ {A : ValuationSubring Ω | IsPlaceOver A v}, Inertia (F := F) A)
    ).topologicalClosure

instance normal_NS : (NS Ω S).Normal := by
  unfold NS; exact Subgroup.is_normal_topologicalClosure _

variable (Ω) in

abbrev GS := G F Ω ⧸ NS Ω S

variable (Ω) in

def toGS : G F Ω →* GS Ω S := QuotientGroup.mk' (NS Ω S)

variable (Ω) in
theorem continuous_toGS : Continuous (toGS Ω S) := QuotientGroup.continuous_mk

end unram

variable (F Ω) in

def cycG [IsAlgClosure F Ω] (n : ℕ) [NeZero n] : G F Ω →* (ZMod n)ˣ :=
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  cycN F Ω n

variable (F Ω) in

structure GData [IsAlgClosure F Ω] (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ) [NeZero n] where

  A : S → ValuationSubring Ω
  hA : ∀ v, IsPlaceOver (A v) v.1

  J : InfinitePlace F → (Ω →+* ℂ)
  hJ : ∀ w, InfinitePlace.mk ((J w).comp (algebraMap F Ω)) = w

  chi : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod n)ˣ
  hchi : chi.comp (toGS Ω _) = cycG F Ω n

variable [IsAlgClosure F Ω] {S : Finset (HeightOneSpectrum (𝓞 F))} {n : ℕ} [NeZero n]

def locGrp (D : GData F Ω S n) : S ⊕ InfinitePlace F → Subgroup (G F Ω) :=
  Sum.elim (fun v => Dec F (D.A v)) (fun w => DecInf F (D.J w))

def locHom (D : GData F Ω S n) (i : S ⊕ InfinitePlace F) :
    locGrp D i →* GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) :=
  (toGS Ω _).comp (locGrp D i).subtype

theorem continuous_locHom (D : GData F Ω S n) (i : S ⊕ InfinitePlace F) :
    Continuous (locHom D i) :=
  (continuous_toGS Ω _).comp continuous_subtype_val

abbrev locF (D : GData F Ω S n) (v : S) := locHom D (Sum.inl v)

theorem continuous_locF (D : GData F Ω S n) (v : S) : Continuous (locF D v) :=
  continuous_locHom D _

instance finite_locGrp_inr (D : GData F Ω S n) (w : InfinitePlace F) :
    Finite (locGrp D (Sum.inr w)) :=
  inferInstanceAs (Finite (DecInf F (D.J w)))

end Global

section PTMaps

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {S : Finset (HeightOneSpectrum (𝓞 F))} {n : ℕ} [NeZero n] (D : GData F Ω S n)
  {M : Type} [AddCommGroup M] [Module (ZMod n) M] [TopologicalSpace M] [DiscreteTopology M]
  (rho : Representation (ZMod n) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)

def Recip (inv : ∀ v : S, H2 ((charRep D.chi).comp (locF D v)) →ₗ[ZMod n] ZMod n) : Prop :=
  ∀ c : H2 (charRep D.chi),
    ∑ v : S, inv v (resH2 (charRep D.chi) (locF D v) (continuous_locF D v) c) = 0

variable (inv : ∀ v : S, H2 ((charRep D.chi).comp (locF D v)) →ₗ[ZMod n] ZMod n)

end PTMaps

section LubinTate

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

def intK : Subring (PadicAlgCl p) where
  carrier := {x | x ∈ K ∧ ‖x‖ ≤ 1}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨K.mul_mem ha hb, ?_⟩
    rw [norm_mul]
    exact mul_le_one₀ ha' (norm_nonneg _) hb'
  one_mem' := ⟨K.one_mem, by simp⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨K.add_mem ha hb, (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha' hb')⟩
  zero_mem' := ⟨K.zero_mem, by simp⟩
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨K.neg_mem ha, by rwa [norm_neg]⟩

abbrev OK : Type := intK p K

variable {p K}

def IsUnif (π : OK p K) : Prop :=
  ‖(π : PadicAlgCl p)‖ < 1 ∧ ∀ x : OK p K, ‖(x : PadicAlgCl p)‖ < 1 → ∃ y : OK p K, x = π * y

def resCard (π : OK p K) : ℕ := Nat.card (OK p K ⧸ Ideal.span {π})

end LubinTate

section Division

variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

def ltPoly (π : OK p K) : Polynomial (PadicAlgCl p) :=
  Polynomial.X ^ resCard π + Polynomial.C (π : PadicAlgCl p) * Polynomial.X

end Division

section Hecke

variable (K : Type) [Field K] [NumberField K]

variable {K}

def infComp (x : Ideles K) (v : InfinitePlace K) : v.Completion := (x : AdeleRing (𝓞 K) K).1 v

def finComp (x : Ideles K) (v : HeightOneSpectrum (𝓞 K)) : v.adicCompletion K :=
  (x : AdeleRing (𝓞 K) K).2 v

def embC (σ : K →+* ℂ) : (InfinitePlace.mk σ).Completion →+* ℂ := by
  classical
  exact if σ = (InfinitePlace.mk σ).embedding then InfinitePlace.Completion.extensionEmbedding _
    else (starRingEnd ℂ).comp (InfinitePlace.Completion.extensionEmbedding _)

end Hecke

end Neutral.B1
