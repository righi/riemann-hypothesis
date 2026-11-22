module

public import ReciprocityTheory.GroupCohomology.CupConnRightStatement
public import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB
public import ReciprocityTheory.GroupCohomology.LowHolds
public import ReciprocityTheory.GroupCohomology.InnerHolds

@[expose] public section

namespace ReciprocityTheory.Coh.InflationRestrictionInvariants

open ReciprocityTheory.Gal Cx Function

universe u

noncomputable section

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

instance instCCSInv (M : TRep R G) (N : Subgroup G) :
    ContinuousConstSMul R (Representation.invariants (M.rho.comp N.subtype)) :=
  ⟨fun c => (continuous_subtype_val.const_smul c).subtype_mk _⟩

abbrev invQ (M : TRep R G) (N : Subgroup G) [N.Normal] : TRep R (G ⧸ N) where
  V := Representation.invariants (M.rho.comp N.subtype)
  rho := Representation.quotientToInvariants M.rho N
  cont := by
    have hq : Topology.IsQuotientMap (fun p : G × Representation.invariants (M.rho.comp N.subtype) =>
        ((p.1 : G ⧸ N), p.2)) :=
      (QuotientGroup.isOpenQuotientMap_mk.prodMap IsOpenQuotientMap.id).isQuotientMap
    unfold Gal.ContAction
    rw [hq.continuous_iff]
    refine Continuous.subtype_mk ?_ _
    exact M.cont.comp ((continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))

def invP (M : TRep R G) (N : Subgroup G) [N.Normal] : Pair (invQ M N) M where
  φ := QuotientGroup.mk' N
  u := (Representation.invariants (M.rho.comp N.subtype)).subtype
  φ_cont := continuous_quot_mk
  u_cont := continuous_subtype_val
  equiv _ _ := rfl

theorem invariants_isInvRep (M : TRep R G) (N : Subgroup G) [N.Normal] : IsInvRep M N (invQ M N) (invP M N) := by
  refine ⟨rfl, Topology.IsEmbedding.subtypeVal, fun m => ?_⟩
  constructor
  · rintro ⟨v, rfl⟩ g hg
    exact v.2 ⟨g, hg⟩
  · intro h
    exact ⟨⟨m, fun g => h g.1 g.2⟩, rfl⟩

end

end ReciprocityTheory.Coh.InflationRestrictionInvariants

namespace ReciprocityTheory.Coh.InflationRestrictionInvariants

open ReciprocityTheory.Gal Cx Function

universe u

noncomputable section

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

abbrev e1 (a : G) : Fin 1 → G := fun _ => a

theorem oneCochain_apply_fin_one (M : TRep R G) (x : M.coch.X 1) (g : Fin 1 → G) : x.1 g = x.1 (e1 (g 0)) :=
  congrArg x.1 (funext fun i => by rw [Fin.fin_one_eq_zero i])

theorem memB {A : Cx R} {n : ℕ} (x : A.X (n + 1)) : x ∈ A.B (n + 1) ↔ ∃ y, A.d n y = x :=
  LinearMap.mem_range

theorem oneDifferential_val (M : TRep R G) (x : M.coch.X 1) (a b : G) :
    (M.coch.d 1 x).1 ![a, b] = M.rho a (x.1 (e1 b)) - x.1 (e1 (a * b)) + x.1 (e1 a) := by
  show ReciprocityTheory.Gal.dn M.rho 1 x.1 ![a, b] = _
  rw [LowDeg.dn_one_apply]
  have he : ∀ c : G, (![c] : Fin 1 → G) = e1 c := fun c => funext fun i => by
    rw [Fin.fin_one_eq_zero i]; rfl
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, he]

theorem wach_d1_eq_zero_iff (M : TRep R G) (x : M.coch.X 1) :
    M.coch.d 1 x = 0 ↔ ∀ a b, x.1 (e1 (a * b)) = x.1 (e1 a) + M.rho a (x.1 (e1 b)) := by
  constructor
  · intro h a b
    have h1 := congrArg (fun y : M.coch.X 2 => y.1 ![a, b]) h
    simp only [oneDifferential_val] at h1
    have h2 : (0 : M.coch.X 2).1 ![a, b] = 0 := rfl
    rw [h2] at h1
    rw [← sub_eq_zero, show x.1 (e1 (a * b)) - (x.1 (e1 a) + M.rho a (x.1 (e1 b))) =
      -(M.rho a (x.1 (e1 b)) - x.1 (e1 (a * b)) + x.1 (e1 a)) by abel, h1, neg_zero]
  · intro h
    apply Subtype.ext
    funext v
    have hv : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hv, oneDifferential_val, h]
    show _ = (0 : M.V)
    abel

theorem zeroDifferential_val (M : TRep R G) (y : M.coch.X 0) (a : G) :
    (M.coch.d 0 y).1 (e1 a) = M.rho a (y.1 ![]) - y.1 ![] := by
  show ReciprocityTheory.Gal.dn M.rho 0 y.1 (e1 a) = _
  rw [LowDeg.dn_zero_apply]

def const0 (M : TRep R G) (m : M.V) : M.coch.X 0 := ⟨fun _ => m, continuous_const⟩

theorem mem_oneCoboundaries_iff (M : TRep R G) (x : M.coch.X 1) :
    x ∈ M.coch.B 1 ↔ ∃ m, ∀ a, x.1 (e1 a) = M.rho a m - m := by
  rw [memB]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.1 ![], fun a => zeroDifferential_val M y a⟩
  · rintro ⟨m, hm⟩
    refine ⟨const0 M m, Subtype.ext (funext fun g => ?_)⟩
    rw [oneCochain_apply_fin_one M x g, hm, oneCochain_apply_fin_one M (M.coch.d 0 (const0 M m)) g, zeroDifferential_val]
    rfl

end

end ReciprocityTheory.Coh.InflationRestrictionInvariants

namespace ReciprocityTheory.Coh.InflationRestrictionInvariants

open ReciprocityTheory.Gal Cx Function

universe u

noncomputable section

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem cocycle_one (M : TRep R G) (x : M.coch.X 1) (hx : M.coch.d 1 x = 0) : x.1 (e1 1) = 0 := by
  have h := (wach_d1_eq_zero_iff M x).mp hx 1 1
  rw [mul_one, map_one, Module.End.one_apply] at h
  have h2 : x.1 (e1 1) + x.1 (e1 1) - x.1 (e1 1) = 0 := by rw [← h]; abel
  simpa using h2

end

end ReciprocityTheory.Coh.InflationRestrictionInvariants

namespace ReciprocityTheory.Coh

open InflationRestrictionInvariants

universe u

end ReciprocityTheory.Coh
