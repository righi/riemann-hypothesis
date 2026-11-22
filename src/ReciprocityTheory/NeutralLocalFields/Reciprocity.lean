module

public import Mathlib

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Topology

namespace Neutral.B1

section Galois

variable (F : Type*) [Field F]

structure IsFiniteAbelian (L : IntermediateField F (AlgebraicClosure F)) : Prop where
  finiteDimensional : FiniteDimensional F L
  isGalois : IsGalois F L
  comm : ∀ a b : L ≃ₐ[F] L, a * b = b * a

def toAb : Field.absoluteGaloisGroup F →* Field.absoluteGaloisGroupAbelianization F :=
  QuotientGroup.mk' _

def abRestrict (L : IntermediateField F (AlgebraicClosure F)) (h : IsFiniteAbelian F L) :
    Field.absoluteGaloisGroupAbelianization F →* (L ≃ₐ[F] L) :=
  haveI := h.finiteDimensional
  haveI := h.isGalois
  letI : CommGroup (L ≃ₐ[F] L) := { (inferInstance : Group (L ≃ₐ[F] L)) with mul_comm := h.comm }
  QuotientGroup.lift _ (AlgEquiv.restrictNormalHom L : Field.absoluteGaloisGroup F →* (L ≃ₐ[F] L))
    (by
      refine Subgroup.topologicalClosure_minimal _ ?_ ?_
      · exact Group.Abelianization.commutator_le_ker _
      · have e : ((AlgEquiv.restrictNormalHom L : Gal(AlgebraicClosure F/F) →* (L ≃ₐ[F] L)).ker :
            Set Gal(AlgebraicClosure F/F)) = (L.fixingSubgroup : Set Gal(AlgebraicClosure F/F)) := by
          rw [IntermediateField.restrictNormalHom_ker]
        have hc : IsClosed ((AlgEquiv.restrictNormalHom L :
            Gal(AlgebraicClosure F/F) →* (L ≃ₐ[F] L)).ker : Set Gal(AlgebraicClosure F/F)) :=
          e ▸ L.fixingSubgroup_isClosed
        exact hc)

theorem abRestrict_mk (L : IntermediateField F (AlgebraicClosure F)) (h : IsFiniteAbelian F L)
    (g : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :
    (haveI := h.isGalois
     abRestrict F L h (toAb F g) = AlgEquiv.restrictNormalHom L g) := by
  unfold abRestrict toAb
  exact QuotientGroup.lift_mk' _ _ _

end Galois

section Local

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]

def IsUniformiser (π : K) : Prop :=
  ∃ hπ : π ∈ 𝒪[K], Irreducible (⟨π, hπ⟩ : 𝒪[K])

def normGroup (L : IntermediateField K (AlgebraicClosure K)) : Subgroup Kˣ :=
  (Units.map (Algebra.norm K : L →* K)).range

end Local

section Global

variable (K : Type*) [Field K] [NumberField K]

abbrev Ideles : Type _ := (AdeleRing (𝓞 K) K)ˣ

def diagUnits : Kˣ →* Ideles K :=
  Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom

abbrev IdeleClassGroup : Type _ := Ideles K ⧸ (diagUnits K).range

def IsUnramifiedIn (v : HeightOneSpectrum (𝓞 K)) (L : Type*) [Field L] [Algebra K L] : Prop :=
  ∀ Q : Ideal (𝓞 L), Q.IsPrime → Q.LiesOver v.asIdeal → Q.ramificationIdx (𝓞 K) = 1

def IsFrobAt (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] (τ : L ≃ₐ[K] L)
    (Q : Ideal (𝓞 L)) : Prop :=
  (galRestrict (𝓞 K) K L (𝓞 L) τ).toAlgHom.IsArithFrobAt Q

def IsComplexConjugationAt (w : InfinitePlace K) (L : Type*) [Field L] [Algebra K L]
    (τ : L ≃ₐ[K] L) : Prop :=
  ∀ φ : L →+* ℂ, φ.comp (algebraMap K L) = w.embedding →
    ∀ x : L, starRingEnd ℂ (φ x) = φ (τ x)

def IsUniformiserAt (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) : Prop :=
  ∃ hx : x ∈ v.adicCompletionIntegers K, Irreducible (⟨x, hx⟩ : v.adicCompletionIntegers K)

def IsSupportedAt (a : Ideles K) (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  (∀ w : InfinitePlace K, (a : AdeleRing (𝓞 K) K).1 w = 1) ∧
  ∀ v' : HeightOneSpectrum (𝓞 K), v' ≠ v → (a : AdeleRing (𝓞 K) K).2 v' = 1

def IsGlobalArtinMap (Art : IdeleClassGroup K →* Field.absoluteGaloisGroupAbelianization K) :
    Prop :=
  Continuous Art ∧ Function.Surjective Art ∧
  ((Art.ker : Set (IdeleClassGroup K)) = connectedComponent 1) ∧
  (∀ (L : IntermediateField K (AlgebraicClosure K)) (h : IsFiniteAbelian K L)
      (v : HeightOneSpectrum (𝓞 K)), IsUnramifiedIn K v L →
      ∀ a : Ideles K, IsSupportedAt K a v →
        (IsUniformiserAt K v ((a : AdeleRing (𝓞 K) K).2 v) →
          ∀ Q : Ideal (𝓞 L), Q.IsPrime → Q.LiesOver v.asIdeal →
            haveI := h.finiteDimensional
            IsFrobAt K L (abRestrict K L h (Art (QuotientGroup.mk a))) Q) ∧
        (Valued.v ((a : AdeleRing (𝓞 K) K).2 v) = 1 →
          abRestrict K L h (Art (QuotientGroup.mk a)) = 1)) ∧
  (∀ (L : IntermediateField K (AlgebraicClosure K)) (h : IsFiniteAbelian K L)
      (w : InfinitePlace K), w.IsReal →
      ∀ a : Ideles K, (∀ v : HeightOneSpectrum (𝓞 K), (a : AdeleRing (𝓞 K) K).2 v = 1) →
        (∀ w' : InfinitePlace K, w' ≠ w → (a : AdeleRing (𝓞 K) K).1 w' = 1) →
        (a : AdeleRing (𝓞 K) K).1 w = -1 →
        IsComplexConjugationAt K w L (abRestrict K L h (Art (QuotientGroup.mk a))))

def rayUnits (m₀ : Ideal (𝓞 K)) (mInf : Set (InfinitePlace K)) : Set (Ideles K) :=
  {a | (∀ w ∈ mInf, IsSquare ((a : AdeleRing (𝓞 K) K).1 w)) ∧
    ∀ v : HeightOneSpectrum (𝓞 K),
      Valued.v ((a : AdeleRing (𝓞 K) K).2 v) = 1 ∧
      ∃ x ∈ m₀, Valued.v ((a : AdeleRing (𝓞 K) K).2 v - 1) ≤
        Valued.v (algebraMap K (v.adicCompletion K) (x : K))}


open scoped Classical in
open Classical in
def finiteSingle (v : HeightOneSpectrum (𝓞 K)) :
    v.adicCompletion K →* FiniteAdeleRing (𝓞 K) K where
  toFun x := RestrictedProduct.mulSingle
    (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletionIntegers K) v x
  map_one' := RestrictedProduct.mulSingle_one _ _
  map_mul' x y := RestrictedProduct.mulSingle_mul _ _ x y

def localIdele (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ →* Ideles K :=
  Units.map
    { toFun := fun x => ((1 : InfiniteAdeleRing K), finiteSingle K v x)
      map_one' := Prod.ext rfl (map_one (finiteSingle K v))
      map_mul' := fun x y => Prod.ext (mul_one 1).symm (map_mul (finiteSingle K v) x y) }

theorem localIdele_snd_self (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    (localIdele K v x : AdeleRing (𝓞 K) K).2 v = x := by
  classical
  show Pi.mulSingle v (x : v.adicCompletion K) v = _
  exact Pi.mulSingle_eq_same v _

theorem localIdele_isSupportedAt (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    IsSupportedAt K (localIdele K v x) v := by
  classical
  refine ⟨fun w => rfl, fun v' hv' => ?_⟩
  show Pi.mulSingle v (x : v.adicCompletion K) v' = 1
  exact Pi.mulSingle_eq_of_ne hv' _

theorem valued_algebraMap_eq_one (v : HeightOneSpectrum (𝓞 K)) (y : 𝓞 K) (hy : y ∉ v.asIdeal) :
    Valued.v (algebraMap K (v.adicCompletion K) (y : K)) = 1 := by
  have e : algebraMap K (v.adicCompletion K) (y : K) =
      ((algebraMap (𝓞 K) K y : K) : v.adicCompletion K) := rfl
  rw [e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    HeightOneSpectrum.valuation_eq_one_iff_notMem]
  exact hy


def localComposite (Art : IdeleClassGroup K →* Field.absoluteGaloisGroupAbelianization K)
    (L : IntermediateField K (AlgebraicClosure K)) (h : IsFiniteAbelian K L)
    (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ →* (L ≃ₐ[K] L) :=
  (abRestrict K L h).comp
    (Art.comp ((QuotientGroup.mk' (diagUnits K).range).comp (localIdele K v)))

theorem exists_isUniformiserAt (v : HeightOneSpectrum (𝓞 K)) :
    ∃ π : (v.adicCompletion K)ˣ, IsUniformiserAt K v (π : v.adicCompletion K) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  have h0 : (ϖ : v.adicCompletion K) ≠ 0 := by
    intro h
    exact hϖ.ne_zero (Subtype.ext h)
  exact ⟨Units.mk0 _ h0, ϖ.2, hϖ⟩

end Global

section Chebotarev

variable (K : Type*) [Field K] [NumberField K]

end Chebotarev

end Neutral.B1
