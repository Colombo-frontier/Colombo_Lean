import Bilevel.ChiOuterJoint
import Bilevel.ChiCarrierFineEnvelope
import Bilevel.ChiCarrierRadialProfile

/-! Actual one-sided outer selector jets through order three. The
disjointness includes mixed derivative orders and all cutoff boundaries. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry
open ZeroChainResidualBounds (projection_norm_le scalar_linear_jet_bound jet_mul_bound jet_mul_zero_left jet_mul_zero_right)

theorem selector_succ_flat_all {n : ℕ} (i : Fin n) (z : Space n)
    (hz : z i.castSucc≤1/2) (k : ℕ) (hk : k≤3) :
    iteratedFDeriv ℝ k (selector n i.succ) z=0 := by
  apply jet_mul_zero_left (psi_contDiff.comp (EuclideanSpace.proj (𝕜:=ℝ) i.castSucc).contDiff)
    (tailMask_contDiff i.succ 3) z k hk
  intro q hq
  apply norm_le_zero_iff.mp
  apply scalar_linear_jet_bound psi_contDiff _ (projection_norm_le _) z q (by omega) 0 le_rfl
  change |iteratedDeriv q psi (z i.castSucc)|≤0
  rw [psi_flat_left q (by omega) _ hz,abs_zero]

theorem selector_flat_large_tail_all {n : ℕ} (i l : Fin (n+1)) (z : Space n)
    (hil : i≤l) (hz : 1/2≤|z l|) (k : ℕ) (hk : k≤3) :
    iteratedFDeriv ℝ k (selector n i) z=0 := by
  have he : 1≤tailEnergy i z := by
    have hh := coordinate_energy_le i l z hil
    simpa only [coordinateCutoff_one hz,one_pow] using hh
  revert he
  refine Fin.cases (fun he => tailMask_flat_jet 0 z he k hk) (fun j he => ?_) i
  exact jet_mul_zero_right (psi_contDiff.comp (EuclideanSpace.proj (𝕜:=ℝ) j.castSucc).contDiff)
    (tailMask_contDiff j.succ 3) z k hk (fun q hq => tailMask_flat_jet j.succ z he q (by omega))

theorem selector_jet_before_later_all {n : ℕ} (i l : Fin (n+1)) (z : Space n)
    (k q : ℕ) (hk : k≤3) (hq : q≤3) (hil : i<l)
    (hl : iteratedFDeriv ℝ q (selector n l) z≠0) :
    iteratedFDeriv ℝ k (selector n i) z=0 := by
  revert hil hl
  refine Fin.cases (by intro h;exact False.elim (Fin.not_lt_zero i h)) (fun j => ?_) l
  intro hij hj
  have hz : 1/2<z j.castSucc := by
    by_contra! hz
    exact hj (selector_succ_flat_all j z hz q hq)
  apply selector_flat_large_tail_all i j.castSucc z _ (hz.le.trans (le_abs_self _)) k hk
  change i.val≤j.val
  change i.val<j.val+1 at hij
  omega

theorem selector_all_jets_unique {n : ℕ} (i l : Fin (n+1)) (z : Space n)
    (k q : ℕ) (hk : k≤3) (hq : q≤3)
    (hi : iteratedFDeriv ℝ k (selector n i) z≠0)
    (hl : iteratedFDeriv ℝ q (selector n l) z≠0) : i=l := by
  rcases lt_trichotomy i l with h|h|h
  · exact False.elim (hi (selector_jet_before_later_all i l z k q hk hq h hl))
  · exact h
  · exact False.elim (hl (selector_jet_before_later_all l i z q k hq hk h hi))

theorem selector_uniform_jets : ∃ B : ℝ,1≤B ∧ ∀ (n : ℕ) (i : Fin (n+1)) (z : Space n)
    (k : ℕ),k≤3 → ‖iteratedFDeriv ℝ k (selector n i) z‖≤B := by
  obtain ⟨K,hK,hprof⟩ := chain_profile_bound
  obtain ⟨M,hM⟩ := mask_control_exists
  have hK0 : 0≤K := by linarith
  have hM0 : 0≤M := by linarith [hM.one_le]
  let B := 1+∑ q : Fin 4,selectorJetBound K M q.val
  have hnonneg (q : Fin 4) : 0≤selectorJetBound K M q.val := selectorJetBound_nonneg hK0 hM0 _
  have hB : 1≤B := by unfold B;exact le_add_of_nonneg_right (Finset.sum_nonneg (fun q _ => hnonneg q))
  have hbB (q : Fin 4) : selectorJetBound K M q.val≤B := by
    have hh := Finset.single_le_sum (fun q (_ : q∈Finset.univ) => hnonneg q) (Finset.mem_univ q)
    unfold B
    linarith
  refine ⟨B,hB,fun n i z k hk => ?_⟩
  apply le_trans _ (hbB ⟨k,by omega⟩)
  have hsum : 0≤∑ q ∈ Finset.range (k+1),(k.choose q:ℝ)*(2*K)*maskJetBound M (k-q) :=
    Finset.sum_nonneg (fun q _ => mul_nonneg (by positivity) (maskJetBound_nonneg hM0 _))
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (tailMask_jet_bound hM 0 z k hk).trans (le_add_of_nonneg_right hsum)
  · have hs := jet_mul_bound (psi_contDiff.comp (EuclideanSpace.proj (𝕜:=ℝ) j.castSucc).contDiff)
      (tailMask_contDiff j.succ 3) z k hk (fun _ => 2*K) (maskJetBound M) (fun _ => by positivity)
      (fun q hq => scalar_linear_jet_bound psi_contDiff _ (projection_norm_le _) z q (by omega)
        (2*K) (by positivity) (((hprof ⟨q,by omega⟩ _).1).trans (by linarith)))
      (fun q hq => tailMask_jet_bound hM j.succ z q (by omega))
    exact hs.trans (le_add_of_nonneg_left (maskJetBound_nonneg hM0 k))

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def jointOuterSelector (m : ℕ) (M : Node E) (i : Fin (M.n+1)) : Joint E (Blocks m F) → ℝ :=
  wrappedSelector M i ∘ outerProjection m

omit [CompleteSpace F] in
theorem jointOuterSelector_contDiff (m : ℕ) (M : Node E) (i : Fin (M.n+1)) :
    ContDiff ℝ 3 (jointOuterSelector (F:=F) m M i) :=
  (wrappedSelector_contDiff M i 3).comp (outerProjection (E:=E) (F:=F) m).contDiff

omit [CompleteSpace E] [CompleteSpace F] in
theorem outerProjection_norm_le (m : ℕ) : ‖outerProjection (E:=E) (F:=F) m‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro z
  exact (WithLp.norm_fst_le E z).trans_eq (one_mul _).symm

omit [CompleteSpace E] [CompleteSpace F] in
theorem innerProjection_norm_le (m : ℕ) : ‖innerProjection (E:=E) (F:=F) m‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro z
  exact (WithLp.norm_snd_le E z).trans_eq (one_mul _).symm

theorem contraction_jet_bound {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (p : X →L[ℝ] Y) (hp : ‖p‖≤1)
    {f : Y → ℝ} (hf : ContDiff ℝ 3 f) (x : X) (k : ℕ) (hk : k≤3) :
    ‖iteratedFDeriv ℝ k (f ∘ p) x‖≤‖iteratedFDeriv ℝ k f (p x)‖ := by
  rw [p.iteratedFDeriv_comp_right hf x (by exact_mod_cast hk)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (pow_le_one₀ (norm_nonneg p) hp) (norm_nonneg _)

omit [CompleteSpace F] in
theorem jointOuterSelector_jets_unique (m : ℕ) (M : Node E) (i l : Fin (M.n+1))
    (z : Joint E (Blocks m F)) (k q : ℕ) (hk : k≤3) (hq : q≤3)
    (hi : iteratedFDeriv ℝ k (jointOuterSelector m M i) z≠0)
    (hl : iteratedFDeriv ℝ q (jointOuterSelector m M l) z≠0) : i=l := by
  have hlatent (a : Fin (M.n+1)) (s : ℕ) (hs : s≤3)
      (ha : iteratedFDeriv ℝ s (jointOuterSelector m M a) z≠0) :
      ∃ t≤s,iteratedFDeriv ℝ t (selector M.n a) (M.width⁻¹ • M.coordinates z.fst)≠0 := by
    by_contra! hzero
    apply ha
    have hc : ContDiff ℝ 3 (fun y : Joint E (Blocks m F) => M.width⁻¹ • M.coordinates y.fst) :=
      ((M.coordinates_contDiff 3).comp (outerProjection (E:=E) (F:=F) m).contDiff).const_smul M.width⁻¹
    exact flat_jet_comp hc (selector_contDiff M.n 3 a) z s hs (fun t ht => by rw [hzero t ht,norm_zero])
  obtain ⟨a,ha,hai⟩ := hlatent i k hk hi
  obtain ⟨b,hb,hbl⟩ := hlatent l q hq hl
  exact selector_all_jets_unique i l _ a b (by omega) (by omega) hai hbl

theorem constructed_outer_selector_jets : ∃ C : ℝ,1≤C ∧
    ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (M : Node E),0<M.width → M.width≤M.radius → ∀ m i (z : Joint E (Blocks m F)) k,k≤3 →
      ‖iteratedFDeriv ℝ k (jointOuterSelector m M i) z‖≤C/M.width^k := by
  obtain ⟨B,hB,hraw⟩ := selector_uniform_jets
  have hB0 : 0≤B := by linarith
  refine ⟨100000*B,by linarith,fun E F _ _ _ _ _ _ M hh hhR m i z k hk => ?_⟩
  apply (contraction_jet_bound (outerProjection (E:=E) (F:=F) m) (outerProjection_norm_le m)
    (wrappedSelector_contDiff M i 3) z k hk).trans
  have hs := scaled_radial_profile_jet_bound (selector_contDiff M.n 3 i) B 1 M.width M.radius
    hB0 (by norm_num) hh hhR (fun q hq y => hraw M.n i y q hq) M.frame z.fst k hk
  simpa only [wrappedSelector,Node.coordinates,Function.comp_def,ZeroChainResidualScaled.scaled,
    one_mul,mul_one] using hs

end Bilevel.ChiOuter
