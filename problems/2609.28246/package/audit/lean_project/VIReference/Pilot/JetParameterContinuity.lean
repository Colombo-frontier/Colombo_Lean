import VIReference.Pilot.BorelRunner
import Mathlib.Analysis.Analytic.IteratedFDeriv

/-!
# Parameter continuity of hidden exact jets

This module gives explicit rank-one tensor formulas for every iterated
Fréchet derivative of the scalar-gate ridge construction.  Those formulas
make continuity in both the hidden frame and query point transparent.
-/

open Set MeasureTheory
open scoped RealInnerProductSpace ContDiff

namespace VIReference.Pilot

noncomputable def gateRidgeIteratedTensor
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n : ℕ) (profile : GateProfile) (tau : ℝ) (a w x : E) :
    E [×n]→L[ℝ] E :=
  ((iteratedDeriv n (gate profile tau) (inner ℝ a x)) •
    ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compContinuousLinearMap
      (fun _ => innerSL ℝ a))).smulRight w

theorem gateRidgeIteratedTensor_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n : ℕ) (profile : GateProfile) (tau : ℝ) (a w x : E)
    (u : Fin n → E) :
    gateRidgeIteratedTensor n profile tau a w x u =
      ((∏ j : Fin n, inner ℝ a (u j)) *
        iteratedDeriv n (gate profile tau) (inner ℝ a x)) • w := by
  simp [gateRidgeIteratedTensor, mul_comm]

theorem continuous_gateRidgeIteratedTensor
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n : ℕ) (profile : GateProfile) {tau : ℝ} (htau : tau ≠ 0) :
    Continuous (fun z : (E × E) × E =>
      gateRidgeIteratedTensor n profile tau z.1.1 z.1.2 z.2) := by
  have hinner : Continuous (fun a : E => innerSL ℝ a) :=
    (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).continuous
  have hfamily : Continuous (fun a : E => fun _ : Fin n => innerSL ℝ a) := by
    exact continuous_pi fun _ => hinner
  have htensor : Continuous (fun a : E =>
      (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compContinuousLinearMap
        (fun _ => innerSL ℝ a)) := by
    have heval : Continuous
        (fun z : (ContinuousMultilinearMap ℝ
            (fun _ : Fin n => E →L[ℝ] ℝ)
            (E [×n]→L[ℝ] ℝ)) ×
            (Fin n → E →L[ℝ] ℝ) => z.1 z.2) := continuous_eval
    have hg : Continuous (fun _ : E =>
        ContinuousMultilinearMap.compContinuousLinearMapLRight
          (E := fun _ : Fin n => E)
          (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ)) :=
      continuous_const
    exact heval.comp (hg.prodMk hfamily)
  have hderiv : Continuous (iteratedDeriv n (gate profile tau)) :=
    (contDiff_infty.mp (gate_contDiff profile htau) n).continuous_iteratedDeriv' n
  have hscalar : Continuous (fun z : (E × E) × E =>
      iteratedDeriv n (gate profile tau) (inner ℝ z.1.1 z.2)) := by
    apply hderiv.comp
    fun_prop
  have hscaled : Continuous (fun z : (E × E) × E =>
      (iteratedDeriv n (gate profile tau) (inner ℝ z.1.1 z.2)) •
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compContinuousLinearMap
          (fun _ => innerSL ℝ z.1.1))) := by
    exact hscalar.smul (htensor.comp (continuous_fst.comp continuous_fst))
  have hsmulRight : Continuous
      (fun z : (E [×n]→L[ℝ] ℝ) × E => z.1.smulRight z.2) :=
    by
      exact ((ContinuousMultilinearMap.smulRightL ℝ
        (fun _ : Fin n => E) E).continuous.comp continuous_fst).clm_apply
          continuous_snd
  exact hsmulRight.comp (hscaled.prodMk (continuous_snd.comp continuous_fst))

theorem gateRidge_iteratedFDeriv_eq_tensor
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n : ℕ) (profile : GateProfile) {tau : ℝ} (htau : tau ≠ 0)
    (a w x : E) :
    iteratedFDeriv ℝ n (gateRidge profile tau a w) x =
      gateRidgeIteratedTensor n profile tau a w x := by
  ext u
  rw [gateRidge_iteratedFDeriv_apply n profile htau,
    gateRidgeIteratedTensor_apply]

noncomputable def truncatedHiddenMapIteratedTensor
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n : ℕ) (profile : GateProfile) (R : ℝ) (N t : ℕ)
    (v : Fin (N + 1) → E) (x : E) : E [×n]→L[ℝ] E :=
  iteratedFDeriv ℝ n
      (fun _ : E => hiddenC R N • v ⟨0, Nat.zero_lt_succ N⟩) 0 +
    hiddenQ N • ∑ i : Fin N, if i.1 < t then
      gateRidgeIteratedTensor n profile (hiddenTau R N)
        (v i.castSucc) (v i.succ) x else 0

theorem truncatedHiddenMap_iteratedFDeriv_eq_tensor
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n : ℕ) (profile : GateProfile) {R : ℝ} (hR : 0 < R)
    (N t : ℕ) (v : Fin (N + 1) → E) (x : E) :
    iteratedFDeriv ℝ n (truncatedHiddenMap profile R N t v) x =
      truncatedHiddenMapIteratedTensor n profile R N t v x := by
  have htau : hiddenTau R N ≠ 0 := (hiddenTau_pos hR N).ne'
  let G : E → E := fun z => ∑ i : Fin N, if i.1 < t then
    gateRidge profile (hiddenTau R N) (v i.castSucc) (v i.succ) z else 0
  have hridge (i : Fin N) : ContDiff ℝ n
      (gateRidge profile (hiddenTau R N) (v i.castSucc) (v i.succ)) := by
    exact ((contDiff_infty.mp (gate_contDiff profile htau) n).comp
      (innerSL ℝ (v i.castSucc)).contDiff).smul_const _
  have hG : ContDiff ℝ n G := by
    apply ContDiff.sum
    intro i _hi
    by_cases hit : i.1 < t
    · simpa only [if_pos hit] using hridge i
    · simp only [if_neg hit]
      exact contDiff_const
  have hqG : ContDiff ℝ n (fun z => hiddenQ N • G z) := hG.const_smul _
  have hmap : truncatedHiddenMap profile R N t v = fun z =>
      hiddenC R N • v ⟨0, Nat.zero_lt_succ N⟩ + hiddenQ N • G z := by
    funext z
    simp only [truncatedHiddenMap, G, gateRidge]
  rw [hmap]
  change iteratedFDeriv ℝ n
      ((fun _ : E => hiddenC R N • v ⟨0, Nat.zero_lt_succ N⟩) +
        fun z => hiddenQ N • G z) x = _
  rw [iteratedFDeriv_add_apply contDiffAt_const hqG.contDiffAt,
    iteratedFDeriv_const_smul_apply' hG.contDiffAt]
  simp only [truncatedHiddenMapIteratedTensor]
  have hconst : iteratedFDeriv ℝ n
      (fun _ : E => hiddenC R N • v ⟨0, Nat.zero_lt_succ N⟩) x =
      iteratedFDeriv ℝ n
      (fun _ : E => hiddenC R N • v ⟨0, Nat.zero_lt_succ N⟩) 0 := by
    by_cases hn : n = 0
    · subst n
      rfl
    · simp [iteratedFDeriv_const_of_ne hn]
  rw [hconst]
  congr 1
  rw [iteratedFDeriv_fun_sum_apply]
  · simp only [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    by_cases hit : i.1 < t
    · simp only [if_pos hit]
      rw [gateRidge_iteratedFDeriv_eq_tensor n profile htau]
    · simp only [if_neg hit]
      have hz : (fun _ : E => (0 : E)) = 0 := rfl
      rw [hz, iteratedFDeriv_zero]
      simp
  · intro i _hi
    by_cases hit : i.1 < t
    · simpa only [if_pos hit] using (hridge i).contDiffAt
    · simp only [if_neg hit]
      exact contDiffAt_const

theorem continuous_truncatedHiddenMapIteratedTensor
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n : ℕ) (profile : GateProfile) {R : ℝ} (hR : 0 < R)
    (N t : ℕ) :
    Continuous (fun z : (Fin (N + 1) → E) × E =>
      truncatedHiddenMapIteratedTensor n profile R N t z.1 z.2) := by
  have htau : hiddenTau R N ≠ 0 := (hiddenTau_pos hR N).ne'
  have hconst : Continuous (fun z : (Fin (N + 1) → E) × E =>
      iteratedFDeriv ℝ n
        (fun _ : E => hiddenC R N • z.1 ⟨0, Nat.zero_lt_succ N⟩) 0) := by
    by_cases hn : n = 0
    · subst n
      have hv : Continuous (fun z : (Fin (N + 1) → E) × E =>
          hiddenC R N • z.1 ⟨0, Nat.zero_lt_succ N⟩) := by fun_prop
      have hu : Continuous (fun z : (Fin (N + 1) → E) × E =>
          ContinuousMultilinearMap.uncurry0 ℝ E
            (hiddenC R N • z.1 ⟨0, Nat.zero_lt_succ N⟩)) :=
        (continuousMultilinearCurryFin0 ℝ E E).symm.continuous.comp hv
      convert hu using 1
      funext z
      ext u
      simp [iteratedFDeriv_zero_apply]
    · have heq : (fun z : (Fin (N + 1) → E) × E =>
          iteratedFDeriv ℝ n
            (fun _ : E => hiddenC R N • z.1 ⟨0, Nat.zero_lt_succ N⟩) 0) =
          fun _ => 0 := by
        funext z
        simp [iteratedFDeriv_const_of_ne hn]
      rw [heq]
      exact continuous_const
  have hridge (i : Fin N) : Continuous
      (fun z : (Fin (N + 1) → E) × E =>
        gateRidgeIteratedTensor n profile (hiddenTau R N)
          (z.1 i.castSucc) (z.1 i.succ) z.2) := by
    have hbase := continuous_gateRidgeIteratedTensor
      (E := E) n profile htau
    have harg : Continuous (fun z : (Fin (N + 1) → E) × E =>
        ((z.1 i.castSucc, z.1 i.succ), z.2)) := by fun_prop
    convert hbase.comp harg using 1 <;> rfl
  have hsum : Continuous (fun z : (Fin (N + 1) → E) × E =>
      ∑ i : Fin N, if i.1 < t then
        gateRidgeIteratedTensor n profile (hiddenTau R N)
          (z.1 i.castSucc) (z.1 i.succ) z.2 else 0) := by
    apply continuous_finset_sum
    intro i _hi
    by_cases hit : i.1 < t
    · simpa only [if_pos hit] using hridge i
    · simp only [if_neg hit]
      exact continuous_const
  simp only [truncatedHiddenMapIteratedTensor]
  exact hconst.add (hsum.const_smul (hiddenQ N))

theorem continuous_truncatedHiddenMap_iteratedFDeriv
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n : ℕ) (profile : GateProfile) {R : ℝ} (hR : 0 < R)
    (N t : ℕ) :
    Continuous (fun z : (Fin (N + 1) → E) × E =>
      iteratedFDeriv ℝ n
        (truncatedHiddenMap profile R N t z.1) z.2) := by
  convert continuous_truncatedHiddenMapIteratedTensor
    (E := E) n profile hR N t using 1
  funext z
  exact truncatedHiddenMap_iteratedFDeriv_eq_tensor
    n profile hR N t z.1 z.2

theorem continuous_iteratedFDeriv_id_parameter'
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n N : ℕ) :
    Continuous (fun z : (Fin (N + 1) → E) × E =>
      iteratedFDeriv ℝ n (id : E → E) z.2) := by
  by_cases hn : n = 0
  · subst n
    have hu : Continuous (fun z : (Fin (N + 1) → E) × E =>
        ContinuousMultilinearMap.uncurry0 ℝ E z.2) :=
      (continuousMultilinearCurryFin0 ℝ E E).symm.continuous.comp continuous_snd
    convert hu using 1
    funext z
    ext u
    simp [iteratedFDeriv_zero_apply]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have heq : (fun z : (Fin (N + 1) → E) × E =>
        iteratedFDeriv ℝ n (id : E → E) z.2) =
        fun _ => iteratedFDeriv ℝ n (id : E → E) 0 := by
      funext z
      exact iteratedFDeriv_id_eq_of_pos hnpos z.2 0
    rw [heq]
    exact continuous_const

theorem truncatedHiddenMap_contDiff_all
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (profile : GateProfile) {R : ℝ} (hR : 0 < R) (N t : ℕ)
    (v : Fin (N + 1) → E) :
    ContDiff ℝ ∞ (truncatedHiddenMap profile R N t v) := by
  have htau : hiddenTau R N ≠ 0 := (hiddenTau_pos hR N).ne'
  apply ContDiff.add
  · fun_prop
  · apply ContDiff.const_smul
    apply ContDiff.sum
    intro i _hi
    by_cases hit : i.1 < t
    · simp only [if_pos hit]
      apply ContDiff.smul_const
      exact (gate_contDiff profile htau).comp
        ((innerSL ℝ (v i.castSucc)).contDiff)
    · simp only [if_neg hit]
      exact contDiff_const

/-- Every truncated hidden operator is smooth to all orders. -/
theorem truncatedHiddenOperator_contDiff_all
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : ℕ) (profile : GateProfile) (Lp : ℝ) {R : ℝ} (hR : 0 < R)
    (N t : ℕ) (v : Fin (N + 1) → E) :
    ContDiff ℝ ∞ (truncatedHiddenOperator p profile Lp R N t v) := by
  apply ContDiff.const_smul
  exact contDiff_id.sub (truncatedHiddenMap_contDiff_all profile hR N t v)

theorem truncatedHiddenOperator_iteratedFDeriv_formula
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n p : ℕ) (profile : GateProfile) (Lp : ℝ) {R : ℝ} (hR : 0 < R)
    (N t : ℕ) (v : Fin (N + 1) → E) (x : E) :
    iteratedFDeriv ℝ n
        (truncatedHiddenOperator p profile Lp R N t v) x =
      hiddenLambda p profile Lp R N •
        (iteratedFDeriv ℝ n (id : E → E) x -
          iteratedFDeriv ℝ n (truncatedHiddenMap profile R N t v) x) := by
  have hmap : ContDiff ℝ n (truncatedHiddenMap profile R N t v) :=
    contDiff_infty.mp (truncatedHiddenMap_contDiff_all profile hR N t v) n
  have hsub : ContDiffAt ℝ n
      (fun y : E => id y - truncatedHiddenMap profile R N t v y) x :=
    contDiffAt_id.sub hmap.contDiffAt
  change iteratedFDeriv ℝ n
      (fun y : E => hiddenLambda p profile Lp R N •
        (id y - truncatedHiddenMap profile R N t v y)) x = _
  rw [iteratedFDeriv_const_smul_apply' hsub]
  congr 1
  change iteratedFDeriv ℝ n
      ((id : E → E) - truncatedHiddenMap profile R N t v) x = _
  exact iteratedFDeriv_sub_apply contDiffAt_id hmap.contDiffAt

theorem continuous_truncatedHiddenOperator_iteratedFDeriv
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n p : ℕ) (profile : GateProfile) (Lp : ℝ) {R : ℝ} (hR : 0 < R)
    (N t : ℕ) :
    Continuous (fun z : (Fin (N + 1) → E) × E =>
      iteratedFDeriv ℝ n
        (truncatedHiddenOperator p profile Lp R N t z.1) z.2) := by
  have hid := continuous_iteratedFDeriv_id_parameter' (E := E) n N
  have hmap := continuous_truncatedHiddenMap_iteratedFDeriv
    (E := E) n profile hR N t
  have hrhs : Continuous (fun z : (Fin (N + 1) → E) × E =>
      hiddenLambda p profile Lp R N •
        (iteratedFDeriv ℝ n (id : E → E) z.2 -
          iteratedFDeriv ℝ n (truncatedHiddenMap profile R N t z.1) z.2)) :=
    (hid.sub hmap).const_smul (hiddenLambda p profile Lp R N)
  convert hrhs using 1
  funext z
  exact truncatedHiddenOperator_iteratedFDeriv_formula
    n p profile Lp hR N t z.1 z.2

theorem continuous_hiddenOperator_iteratedFDeriv
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n p : ℕ) (profile : GateProfile) (Lp : ℝ) {R : ℝ} (hR : 0 < R)
    (N : ℕ) :
    Continuous (fun z : (Fin (N + 1) → E) × E =>
      iteratedFDeriv ℝ n
        (hiddenOperator p profile Lp R N z.1) z.2) := by
  have h := continuous_truncatedHiddenOperator_iteratedFDeriv
    (E := E) n p profile Lp hR N N
  have hop (v : Fin (N + 1) → E) :
      hiddenOperator p profile Lp R N v =
        truncatedHiddenOperator p profile Lp R N N v := by
    funext x
    simp only [truncatedHiddenOperator, hiddenOperator]
    rw [truncatedHiddenMap_of_ge profile R N N le_rfl]
  have heq : (fun z : (Fin (N + 1) → E) × E =>
      iteratedFDeriv ℝ n
        (hiddenOperator p profile Lp R N z.1) z.2) =
      (fun z => iteratedFDeriv ℝ n
        (truncatedHiddenOperator p profile Lp R N N z.1) z.2) := by
    funext z
    rw [hop z.1]
  rw [heq]
  exact h


theorem iteratedFDeriv_id_eq_zero_of_two_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n : ℕ) (hn : 2 ≤ n) (x : E) :
    iteratedFDeriv ℝ n (id : E → E) x = 0 := by
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero => omega
    | succ k =>
      ext u
      rw [iteratedFDeriv_succ_apply_right]
      simp only [fderiv_id]
      rw [iteratedFDeriv_const_of_ne (by omega : k + 1 ≠ 0)]
      simp

theorem gateRidgeIteratedTensor_symmetric
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n : ℕ) (profile : GateProfile) (tau : ℝ) (a w x : E) :
    IsSymmetricContinuousMultilinearMap E
      (gateRidgeIteratedTensor n profile tau a w x) := by
  intro sigma
  ext u
  rw [ContinuousMultilinearMap.domDomCongr_apply,
    gateRidgeIteratedTensor_apply, gateRidgeIteratedTensor_apply]
  congr 2
  exact Equiv.prod_comp sigma (fun j => inner ℝ a (u j))

theorem constantIteratedFDeriv_symmetric
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n : ℕ) (c : E) :
    IsSymmetricContinuousMultilinearMap E
      (iteratedFDeriv ℝ n (fun _ : E => c) 0) := by
  intro sigma
  by_cases hn : n = 0
  · subst n
    ext u
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    congr 1
    exact Subsingleton.elim _ _
  · simp [iteratedFDeriv_const_of_ne hn]
    ext u
    simp [ContinuousMultilinearMap.domDomCongr_apply]

theorem truncatedHiddenMapIteratedTensor_symmetric
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n : ℕ) (profile : GateProfile) (R : ℝ) (N t : ℕ)
    (v : Fin (N + 1) → E) (x : E) :
    IsSymmetricContinuousMultilinearMap E
      (truncatedHiddenMapIteratedTensor n profile R N t v x) := by
  intro sigma
  ext u
  simp only [ContinuousMultilinearMap.domDomCongr_apply,
    truncatedHiddenMapIteratedTensor, add_apply, smul_apply]
  congr 1
  · have hc := constantIteratedFDeriv_symmetric n
      (hiddenC R N • v ⟨0, Nat.zero_lt_succ N⟩)
    have happ := congrArg (fun f : E [×n]→L[ℝ] E => f u) (hc sigma)
    simpa only [ContinuousMultilinearMap.domDomCongr_apply] using happ
  · apply congrArg (fun y : E => hiddenQ N • y)
    rw [sum_apply, sum_apply]
    apply Finset.sum_congr rfl
    intro i _hi
    by_cases hit : i.1 < t
    · simp only [if_pos hit]
      have hr := gateRidgeIteratedTensor_symmetric n profile (hiddenTau R N)
        (v i.castSucc) (v i.succ) x
      have happ := congrArg (fun f : E [×n]→L[ℝ] E => f u) (hr sigma)
      simpa only [ContinuousMultilinearMap.domDomCongr_apply] using happ
    · simp [hit]

theorem truncatedHiddenMap_iteratedFDeriv_symmetric
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n : ℕ) (profile : GateProfile) {R : ℝ} (hR : 0 < R)
    (N t : ℕ) (v : Fin (N + 1) → E) (x : E) :
    IsSymmetricContinuousMultilinearMap E
      (iteratedFDeriv ℝ n (truncatedHiddenMap profile R N t v) x) := by
  rw [truncatedHiddenMap_iteratedFDeriv_eq_tensor n profile hR N t v x]
  exact truncatedHiddenMapIteratedTensor_symmetric n profile R N t v x

theorem iteratedFDeriv_id_symmetric
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n : ℕ) (x : E) :
    IsSymmetricContinuousMultilinearMap E
      (iteratedFDeriv ℝ n (id : E → E) x) := by
  intro sigma
  cases n with
  | zero =>
      ext u
      rw [ContinuousMultilinearMap.domDomCongr_apply]
      congr 1
      exact Subsingleton.elim _ _
  | succ n =>
    cases n with
    | zero =>
        have hsigma : sigma = 1 := by
          ext i
          fin_cases i
          simp
        subst sigma
        ext u
        simp [ContinuousMultilinearMap.domDomCongr_apply]
    | succ k =>
        rw [iteratedFDeriv_id_eq_zero_of_two_le (k + 2) (by omega) x]
        ext u
        simp [ContinuousMultilinearMap.domDomCongr_apply]

theorem symmetric_const_smul_sub
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} {A B : E [×n]→L[ℝ] E}
    (hA : IsSymmetricContinuousMultilinearMap E A)
    (hB : IsSymmetricContinuousMultilinearMap E B) (c : ℝ) :
    IsSymmetricContinuousMultilinearMap E (c • (A - B)) := by
  intro sigma
  ext u
  simp only [ContinuousMultilinearMap.domDomCongr_apply, smul_apply, sub_apply]
  have ha := congrArg (fun f : E [×n]→L[ℝ] E => f u) (hA sigma)
  have hb := congrArg (fun f : E [×n]→L[ℝ] E => f u) (hB sigma)
  simp only [ContinuousMultilinearMap.domDomCongr_apply] at ha hb
  rw [ha, hb]

theorem truncatedHiddenOperator_iteratedFDeriv_symmetric
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n p : ℕ) (profile : GateProfile) (Lp : ℝ) {R : ℝ} (hR : 0 < R)
    (N t : ℕ) (v : Fin (N + 1) → E) (x : E) :
    IsSymmetricContinuousMultilinearMap E
      (iteratedFDeriv ℝ n
        (truncatedHiddenOperator p profile Lp R N t v) x) := by
  rw [truncatedHiddenOperator_iteratedFDeriv_formula
    n p profile Lp hR N t v x]
  exact symmetric_const_smul_sub
    (iteratedFDeriv_id_symmetric n x)
    (truncatedHiddenMap_iteratedFDeriv_symmetric
      n profile hR N t v x) _

theorem hiddenOperator_iteratedFDeriv_symmetric
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n p : ℕ) (profile : GateProfile) (Lp : ℝ) {R : ℝ} (hR : 0 < R)
    (N : ℕ) (v : Fin (N + 1) → E) (x : E) :
    IsSymmetricContinuousMultilinearMap E
      (iteratedFDeriv ℝ n (hiddenOperator p profile Lp R N v) x) := by
  have hop : hiddenOperator p profile Lp R N v =
      truncatedHiddenOperator p profile Lp R N N v := by
    funext y
    simp only [hiddenOperator, truncatedHiddenOperator]
    rw [truncatedHiddenMap_of_ge profile R N N le_rfl]
  rw [hop]
  exact truncatedHiddenOperator_iteratedFDeriv_symmetric
    n p profile Lp hR N N v x

section CanonicalOracles

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

noncomputable def truncatedHiddenExactOracle
    (p : ℕ) (hp : 2 ≤ p) (profile : GateProfile)
    (Lp : ℝ) (hLp : 0 < Lp) (R : ℝ) (hR : 0 < R)
    (N : ℕ) (t : Fin N) (v : Fin (N + 1) → E) :
    ExactSymmetricJetOracle
      (ballVIData (E := E) p hp Lp hLp R hR)
      (truncatedHiddenOperator p profile Lp R N t.1 v) :=
  ExactSymmetricJetOracle.ofSymmetricDerivatives
    (ballVIData (E := E) p hp Lp hLp R hR)
    (truncatedHiddenOperator p profile Lp R N t.1 v)
    (fun x j _sigma => truncatedHiddenOperator_iteratedFDeriv_symmetric
      j.1 p profile Lp hR N t.1 v x _sigma)

noncomputable def finalHiddenExactOracle
    (p : ℕ) (hp : 2 ≤ p) (profile : GateProfile)
    (Lp : ℝ) (hLp : 0 < Lp) (R : ℝ) (hR : 0 < R)
    (N : ℕ) (v : Fin (N + 1) → E) :
    ExactSymmetricJetOracle
      (ballVIData (E := E) p hp Lp hLp R hR)
      (hiddenOperator p profile Lp R N v) :=
  ExactSymmetricJetOracle.ofSymmetricDerivatives
    (ballVIData (E := E) p hp Lp hLp R hR)
    (hiddenOperator p profile Lp R N v)
    (fun x j _sigma => hiddenOperator_iteratedFDeriv_symmetric
      j.1 p profile Lp hR N v x _sigma)

end CanonicalOracles

end VIReference.Pilot
