import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open ValuativeRel

namespace GlobalTheory.NormBall

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

open MeasureTheory Matrix in
open ValuativeRel in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private lemma eval_zero_quadratic_mem_maximalIdeal (t : F) (ht : valuation F t < 1) (htmem : t ∈ 𝒪[F]) :
    Polynomial.eval 0 (Polynomial.X ^ 2 + Polynomial.X + Polynomial.C (⟨t, htmem⟩ : 𝒪[F]) :
      Polynomial 𝒪[F]) ∈ IsLocalRing.maximalIdeal 𝒪[F] := by
  simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    zero_pow two_ne_zero, zero_add]
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers _).isUnit_iff_valuation_eq_one]
  exact ht.ne

open MeasureTheory Matrix in
open ValuativeRel in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private lemma exists_sq_eq_one_sub_four_mul {t : F} (ht : valuation F t < 1) :
    ∃ w : F, (1 + 2 * w) ^ 2 = 1 - 4 * t := by
  letI := IsTopologicalAddGroup.rightUniformSpace F
  haveI := isUniformAddGroup_of_addCommGroup (G := F)
  have hH : HenselianRing 𝒪[F] (IsLocalRing.maximalIdeal 𝒪[F]) :=
    IsAdicComplete.henselianRing _ _
  have htmem : t ∈ 𝒪[F] := (Valuation.mem_integer_iff _ _).2 ht.le
  have hf : (Polynomial.X ^ 2 + Polynomial.X + Polynomial.C (⟨t, htmem⟩ : 𝒪[F]) :
      Polynomial 𝒪[F]).Monic := by
    monicity!
  have h1 : IsUnit ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[F]))
      (Polynomial.eval 0 (Polynomial.derivative (Polynomial.X ^ 2 + Polynomial.X +
        Polynomial.C (⟨t, htmem⟩ : 𝒪[F]) : Polynomial 𝒪[F])))) := by
    simp [Polynomial.derivative_X_pow]
  obtain ⟨w, hw, -⟩ := hH.is_henselian _ hf 0 (eval_zero_quadratic_mem_maximalIdeal t ht htmem) h1
  refine ⟨(w : F), ?_⟩
  have h := congrArg (fun x : 𝒪[F] => (x : F)) hw.eq_zero
  simp at h
  linear_combination 4 * h

open MeasureTheory Matrix in
open ValuativeRel in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private lemma valuation_two_le_one : valuation F (2 : F) ≤ 1 := by
  rw [← one_add_one_eq_two]
  exact (valuation F).map_add_le (by simp) (by simp)

open MeasureTheory Matrix in
open ValuativeRel in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private lemma mem_union_of_valuation_sq_le (u : Fˣ) {y : F} (h : valuation F y ^ 2 ≤ valuation F (u : F)) :
    y ∈ _root_.GlobalTheory.SplitWeil.cball (1 : Fˣ) ∪ _root_.GlobalTheory.SplitWeil.cball u := by
  simp only [_root_.GlobalTheory.SplitWeil.cball, Set.mem_union, Set.mem_setOf_eq, Units.val_one, map_one]
  by_cases hy : valuation F y ≤ 1
  · exact Or.inl hy
  · right
    push_neg at hy
    calc valuation F y = valuation F y * 1 := (mul_one _).symm
      _ ≤ valuation F y * valuation F y := by gcongr
      _ = valuation F y ^ 2 := (sq _).symm
      _ ≤ _ := h

open MeasureTheory Matrix in
open ValuativeRel in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private lemma isCompact_isOpen_normFormBall {d : F} (hd : ∀ r : F, r ^ 2 ≠ d) (hd0 : d ≠ 0)
    (h2 : (2 : F) ≠ 0) (s : Fˣ) :
    IsCompact ((_root_.GlobalTheory.NormBall.ballSub hd s : AddSubgroup (F × F)) : Set (F × F)) ∧
      IsOpen ((_root_.GlobalTheory.NormBall.ballSub hd s : AddSubgroup (F × F)) : Set (F × F)) := by
  haveI := (_root_.GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := F)).2
  have hq : Continuous fun p : F × F => p.1 ^ 2 - d * p.2 ^ 2 := by fun_prop
  have hset : ((_root_.GlobalTheory.NormBall.ballSub hd s : AddSubgroup (F × F)) : Set (F × F)) =
      (fun p : F × F => p.1 ^ 2 - d * p.2 ^ 2) ⁻¹' _root_.GlobalTheory.SplitWeil.cball s := rfl
  refine ⟨?_, ?_⟩
  · set D : Fˣ := Units.mk0 d hd0
    set K₁ := (fun y : F => (2 : F)⁻¹ * y) ''
      (_root_.GlobalTheory.SplitWeil.cball (1 : Fˣ) ∪ _root_.GlobalTheory.SplitWeil.cball s)
    set K₂ := (fun y : F => (2 * d)⁻¹ * y) ''
      (_root_.GlobalTheory.SplitWeil.cball (1 : Fˣ) ∪ _root_.GlobalTheory.SplitWeil.cball (D * s))
    have hK₁ : IsCompact K₁ :=
      ((_root_.GlobalTheory.SplitWeil.isCompact_cball _).union (_root_.GlobalTheory.SplitWeil.isCompact_cball _)).image
        (continuous_const.mul continuous_id)
    have hK₂ : IsCompact K₂ :=
      ((_root_.GlobalTheory.SplitWeil.isCompact_cball _).union (_root_.GlobalTheory.SplitWeil.isCompact_cball _)).image
        (continuous_const.mul continuous_id)
    have hclosed : IsClosed ((_root_.GlobalTheory.NormBall.ballSub hd s : AddSubgroup (F × F)) : Set (F × F)) := by
      rw [hset]
      exact (_root_.GlobalTheory.SplitWeil.isCompact_cball s).isClosed.preimage hq
    refine (hK₁.prod hK₂).of_isClosed_subset hclosed ?_
    rintro ⟨a, b⟩ hp
    have hp' : valuation F (a ^ 2 - d * b ^ 2) ≤ valuation F (s : F) := hp
    refine ⟨⟨2 * a, mem_union_of_valuation_sq_le s ?_, by field_simp⟩,
      ⟨2 * (d * b), mem_union_of_valuation_sq_le (D * s) ?_, by field_simp⟩⟩
    · rw [← map_pow]
      exact (by simpa [map_pow] using _root_.GlobalTheory.NormBall.val_trace_sq_le hd a b : valuation F ((2 * a) ^ 2) ≤ _).trans hp'
    · have k := _root_.GlobalTheory.NormBall.val_trace_sq_le hd (d * b) a
      have e : (d * b) ^ 2 - d * a ^ 2 = -d * (a ^ 2 - d * b ^ 2) := by ring
      rw [e, map_mul (valuation F) (-d), Valuation.map_neg] at k
      refine k.trans ?_
      simp only [D, Units.val_mul, Units.val_mk0, map_mul]
      gcongr
  · rw [hset]
    exact (_root_.GlobalTheory.SplitWeil.isOpen_cball s).preimage hq

end GlobalTheory.NormBall
