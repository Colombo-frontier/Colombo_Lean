import Mathlib
import PaperAudit.Frontier05

open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 10000000


section
-- Source component: SingleLowerOneBoundaryReply.lean

open scoped BigOperators ContDiff Topology

namespace FangqingSingleLowerOneBoundaryReply

open FangqingSingleLowerPhysicalGradient FangqingSingleLowerAllDerivativeOracle
  FangqingSingleLowerLocalizedOracleLocality

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def maskedFrame (n k : ℕ) (V : Fin (n + 1) → E) : Fin (n + 1) → E :=
  fun i => if i.val < k then V i else 0

theorem actual_entire_reply_equals_one_boundary_prefix (theta : ℝ → ℝ)
    (htheta : ∀ t, 49 / 16 ≤ t → theta t = 0) (R : ℝ) (hR : 0 < R)
    (n k : ℕ) (V : Fin (n + 1) → E) (x : E)
    (hsmall : ∀ i : Fin (n + 1), k ≤ i.val →
      |inner ℝ (V i) (clippedCandidate R x)| ≤ 1 / 4) :
    allDerivativeOracle (localizedChain theta R n V) x =
      allDerivativeOracle (localizedChain theta R n (maskedFrame n (k + 1) V)) x := by
  by_cases hx : ‖x‖ ≤ 2 * R
  · have hs : ∀ i : Fin (n + 1), k ≤ i.val → |inner ℝ (V i) x| < 1 / 2 := by
      intro i hi
      have hh := hsmall i hi
      simp only [clippedCandidate, if_pos hx] at hh
      linarith only [hh]
    apply actual_localized_entire_oracle_uses_one_boundary theta R n k V (maskedFrame n (k + 1) V)
    · intro i hi
      simp only [maskedFrame, if_pos (by omega : i.val < k + 1)]
    · exact hs
    · intro i hi
      unfold maskedFrame
      split_ifs
      · exact hs i hi
      · simp
  · have ho : 2 * R ≤ ‖x‖ := (lt_of_not_ge hx).le
    rw [actual_localized_entire_oracle_is_public_outside theta htheta R hR n V x ho,
      actual_localized_entire_oracle_is_public_outside theta htheta R hR n
        (maskedFrame n (k + 1) V) x ho]

end
end FangqingSingleLowerOneBoundaryReply
end

section
-- Source component: SingleLowerScalarJetBounds.lean

open scoped BigOperators ContDiff Topology

namespace FangqingSingleLowerScalarJetBounds

open FangqingSingleLowerScalarProfiles

noncomputable section
set_option maxHeartbeats 3500000

theorem bounded_iterated_jets_of_plateaus (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f)
    (a b left right : ℝ)
    (hl : ∀ t, t < a → f t = left) (hr : ∀ t, b < t → f t = right) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j, j ≤ 3 → ∀ t, ‖iteratedFDeriv ℝ j f t‖ ≤ C := by
  classical
  have heach : ∀ j : Fin 4, ∃ C : ℝ, 0 ≤ C ∧ ∀ t, ‖iteratedFDeriv ℝ j.val f t‖ ≤ C := by
    intro j
    have hc : Continuous (iteratedFDeriv ℝ j.val f) := hf.continuous_iteratedFDeriv (by exact_mod_cast (by omega : j.val ≤ 3))
    obtain ⟨C0, hC0⟩ := (isCompact_Icc : IsCompact (Set.Icc a b)).exists_bound_of_continuousOn hc.continuousOn
    let C := max C0 (max ‖left‖ ‖right‖)
    have hC : 0 ≤ C := (norm_nonneg left).trans ((le_max_left _ _).trans (le_max_right _ _))
    refine ⟨C, hC, ?_⟩
    intro t
    by_cases hlo : t < a
    · have heq : f =ᶠ[𝓝 t] (fun _ => left) := by
        filter_upwards [Iio_mem_nhds hlo] with u hu
        exact hl u hu
      rw [(heq.iteratedFDeriv ℝ j.val).eq_of_nhds]
      by_cases hj : j.val = 0
      · rw [hj, norm_iteratedFDeriv_zero]
        exact (le_max_left _ _).trans (le_max_right _ _)
      · rw [iteratedFDeriv_const_of_ne hj]
        simpa using hC
    · by_cases hhi : b < t
      · have heq : f =ᶠ[𝓝 t] (fun _ => right) := by
          filter_upwards [Ioi_mem_nhds hhi] with u hu
          exact hr u hu
        rw [(heq.iteratedFDeriv ℝ j.val).eq_of_nhds]
        by_cases hj : j.val = 0
        · rw [hj, norm_iteratedFDeriv_zero]
          exact (le_max_right _ _).trans (le_max_right _ _)
        · rw [iteratedFDeriv_const_of_ne hj]
          simpa using hC
      · exact (hC0 t ⟨le_of_not_gt hlo, le_of_not_gt hhi⟩).trans (le_max_left _ _)
  choose C hC using heach
  refine ⟨∑ j, C j, Finset.sum_nonneg (fun j _ => (hC j).1), ?_⟩
  intro j hj t
  let jj : Fin 4 := ⟨j, by omega⟩
  exact ((hC jj).2 t).trans (Finset.single_le_sum (fun k _ => (hC k).1) (Finset.mem_univ jj))

theorem psi_iterated_jets_bounded :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j, j ≤ 3 → ∀ t, ‖iteratedFDeriv ℝ j psi t‖ ≤ C := by
  apply bounded_iterated_jets_of_plateaus psi (psi_smooth.of_le (by decide)) 0 1 0 1
  · intro t ht
    exact psi_zero t (by linarith only [ht])
  · intro t ht
    exact psi_one t ht.le

def phiD1 (t : ℝ) : ℝ := 2 / (1 + t ^ 2)
def phiD2 (t : ℝ) : ℝ := -4 * t / (1 + t ^ 2) ^ 2
def phiD3 (t : ℝ) : ℝ := (12 * t ^ 2 - 4) / (1 + t ^ 2) ^ 3

theorem phiD1_hasDerivAt (t : ℝ) : HasDerivAt phiD1 (phiD2 t) t := by
  have hd : HasDerivAt (fun u : ℝ => 1 + u ^ 2) (2 * t) t := by
    convert! ((hasDerivAt_id t).pow 2).const_add 1 using 1 <;> simp only [id_eq] <;> ring
  have hh := (hasDerivAt_const t (2 : ℝ)).div hd (by positivity : (1 + t ^ 2) ≠ 0)
  convert! hh using 1 <;> dsimp [phiD1, phiD2] <;> field_simp <;> ring

theorem phiD2_hasDerivAt (t : ℝ) : HasDerivAt phiD2 (phiD3 t) t := by
  have hd : HasDerivAt (fun u : ℝ => 1 + u ^ 2) (2 * t) t := by
    convert! ((hasDerivAt_id t).pow 2).const_add 1 using 1 <;> simp only [id_eq] <;> ring
  have hn := (hasDerivAt_id t).const_mul (-4 : ℝ)
  have hh := hn.div (hd.pow 2) (by positivity : (1 + t ^ 2) ^ 2 ≠ 0)
  convert! hh using 1 <;> dsimp [phiD2, phiD3] <;> field_simp <;> ring

theorem phi_second_deriv (t : ℝ) : deriv (deriv phi) t = phiD2 t := by
  have heq : deriv phi = phiD1 := funext phi_deriv
  rw [heq]
  exact (phiD1_hasDerivAt t).deriv

theorem phi_iterated_two : iteratedDeriv 2 phi = phiD2 := by
  rw [show (2 : ℕ) = 1 + 1 by decide, iteratedDeriv_succ, iteratedDeriv_one]
  exact funext phi_second_deriv

theorem phi_iterated_three : iteratedDeriv 3 phi = phiD3 := by
  rw [show (3 : ℕ) = 2 + 1 by decide, iteratedDeriv_succ, phi_iterated_two]
  exact funext (fun t => (phiD2_hasDerivAt t).deriv)

theorem phiD2_abs_bound (t : ℝ) : |phiD2 t| ≤ 4 := by
  let d := 1 + t ^ 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : 1 ≤ d := by dsimp [d]; nlinarith only [sq_nonneg t]
  have ha : |t| ≤ d := by
    have hs := sq_nonneg (|t| - 1)
    have heq := sq_abs t
    dsimp [d]
    nlinarith only [hs, heq]
  have hdd : d ≤ d ^ 2 := by nlinarith only [hd1, sq_nonneg (d - 1)]
  change |(-4 : ℝ) * t / d ^ 2| ≤ 4
  rw [abs_div, abs_mul, abs_of_pos (pow_pos hd 2)]
  norm_num only [abs_neg]
  apply (div_le_iff₀ (pow_pos hd 2)).mpr
  nlinarith only [ha, hdd]

theorem phiD3_abs_bound (t : ℝ) : |phiD3 t| ≤ 16 := by
  let d := 1 + t ^ 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : 1 ≤ d := by dsimp [d]; nlinarith only [sq_nonneg t]
  have hnum : |12 * t ^ 2 - 4| ≤ 16 * d := by
    rw [abs_le]
    dsimp [d]
    constructor <;> nlinarith only [sq_nonneg t]
  have hdd : d ≤ d ^ 3 := by
    have hs : (1 : ℝ) ≤ d ^ 2 := one_le_pow₀ hd1
    have hm := mul_le_mul_of_nonneg_left hs hd.le
    nlinarith only [hm]
  change |(12 * t ^ 2 - 4) / d ^ 3| ≤ 16
  rw [abs_div, abs_of_pos (pow_pos hd 3)]
  exact (div_le_iff₀ (pow_pos hd 3)).mpr (hnum.trans (mul_le_mul_of_nonneg_left hdd (by norm_num)))

theorem phi_iterated_jets_bound (j : ℕ) (hj : j ≤ 3) (t : ℝ) :
    ‖iteratedFDeriv ℝ j phi t‖ ≤ 2 * Real.pi + 16 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  interval_cases j
  · simp only [iteratedDeriv_zero, Real.norm_eq_abs, abs_of_pos (phi_range t).1]
    linarith only [(phi_range t).2]
  · rw [iteratedDeriv_one]
    have hb := phi_slope_bounds t
    rw [Real.norm_eq_abs, abs_of_pos hb.1]
    linarith only [hb.2, Real.pi_pos]
  · rw [phi_iterated_two, Real.norm_eq_abs]
    linarith only [phiD2_abs_bound t, Real.pi_pos]
  · rw [phi_iterated_three, Real.norm_eq_abs]
    linarith only [phiD3_abs_bound t, Real.pi_pos]

end
end FangqingSingleLowerScalarJetBounds
end

section
-- Source component: SingleLowerEdgeJetBounds.lean

open scoped BigOperators ContDiff

namespace FangqingSingleLowerEdgeJetBounds

open FangqingSingleLowerScalarProfiles FangqingSingleLowerChainEdge
  FangqingSingleLowerScalarJetBounds FangqingRelayProductBounds

noncomputable section
set_option maxHeartbeats 3500000

def fstP : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
def sndP : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ

theorem fstP_norm_le : ‖fstP‖ ≤ 1 := by
  apply fstP.opNorm_le_bound (by norm_num)
  intro p
  change ‖p.1‖ ≤ 1 * ‖p‖
  simpa only [one_mul] using norm_fst_le p

theorem sndP_norm_le : ‖sndP‖ ≤ 1 := by
  apply sndP.opNorm_le_bound (by norm_num)
  intro p
  change ‖p.2‖ ≤ 1 * ‖p‖
  simpa only [one_mul] using norm_snd_le p

theorem product_uniform_jets
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f g : X → ℝ) (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    (x : X) (Kf Kg : ℝ)
    (hF : ∀ i, i ≤ 3 → ‖iteratedFDeriv ℝ i f x‖ ≤ Kf)
    (hG : ∀ i, i ≤ 3 → ‖iteratedFDeriv ℝ i g x‖ ≤ Kg)
    (j : ℕ) (hj : j ≤ 3) :
    ‖iteratedFDeriv ℝ j (fun z => f z * g z) x‖ ≤ (2 : ℝ) ^ j * Kf * Kg := by
  have hh := product_iterated_bound f g 3 hf hg x j (by exact_mod_cast hj)
    (fun _ => Kf) (fun _ => Kg) (fun i hi => hF i (hi.trans hj)) (fun i hi => hG i (hi.trans hj))
  have hs : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * Kf * Kg) = (2 : ℝ) ^ j * Kf * Kg := by
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    have hchoose : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = (2 : ℝ) ^ j := by
      exact_mod_cast Nat.sum_range_choose j
    rw [hchoose]
  exact hs ▸ hh

theorem scalar_coordinate_jets_bound
    (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) (P : (ℝ × ℝ) →L[ℝ] ℝ) (hP : ‖P‖ ≤ 1)
    (K : ℝ) (hK : ∀ j, j ≤ 3 → ∀ t, ‖iteratedFDeriv ℝ j f t‖ ≤ K)
    (p : ℝ × ℝ) (j : ℕ) (hj : j ≤ 3) :
    ‖iteratedFDeriv ℝ j (f ∘ P) p‖ ≤ K :=
  (norm_iterated_comp_contraction f P 3 hf hP p j (by exact_mod_cast hj)).trans (hK j hj (P p))

theorem actual_edge_jets_from_scalar_bounds
    (Kpsi Kphi : ℝ) (hKpsi : 0 ≤ Kpsi) (hKphi : 0 ≤ Kphi)
    (hpsi : ∀ j, j ≤ 3 → ∀ t, ‖iteratedFDeriv ℝ j psi t‖ ≤ Kpsi)
    (hphi : ∀ j, j ≤ 3 → ∀ t, ‖iteratedFDeriv ℝ j phi t‖ ≤ Kphi)
    (p : ℝ × ℝ) (j : ℕ) (hj : j ≤ 3) :
    ‖iteratedFDeriv ℝ j edge p‖ ≤ 16 * Kpsi * Kphi := by
  let fp := psi ∘ fstP
  let gp := phi ∘ sndP
  let fn := psi ∘ (-fstP)
  let gn := phi ∘ (-sndP)
  have hsPsi : ContDiff ℝ 3 psi := psi_smooth.of_le (by decide)
  have hsPhi : ContDiff ℝ 3 phi := phi_smooth.of_le (by decide)
  have hfp : ContDiff ℝ 3 fp := hsPsi.comp fstP.contDiff
  have hgp : ContDiff ℝ 3 gp := hsPhi.comp sndP.contDiff
  have hfn : ContDiff ℝ 3 fn := hsPsi.comp (-fstP).contDiff
  have hgn : ContDiff ℝ 3 gn := hsPhi.comp (-sndP).contDiff
  have hnegF : ‖-fstP‖ ≤ 1 := by simpa only [norm_neg] using fstP_norm_le
  have hnegG : ‖-sndP‖ ≤ 1 := by simpa only [norm_neg] using sndP_norm_le
  have hp := product_uniform_jets fp gp hfp hgp p Kpsi Kphi
    (fun i hi => scalar_coordinate_jets_bound psi hsPsi fstP fstP_norm_le Kpsi hpsi p i hi)
    (fun i hi => scalar_coordinate_jets_bound phi hsPhi sndP sndP_norm_le Kphi hphi p i hi) j hj
  have hn := product_uniform_jets fn gn hfn hgn p Kpsi Kphi
    (fun i hi => scalar_coordinate_jets_bound psi hsPsi (-fstP) hnegF Kpsi hpsi p i hi)
    (fun i hi => scalar_coordinate_jets_bound phi hsPhi (-sndP) hnegG Kphi hphi p i hi) j hj
  have heq : edge = (fun z => fn z * gn z - fp z * gp z) := by
    funext z
    simp [edge, fn, gn, fp, gp, fstP, sndP, Function.comp_def]
  have hjN : (j : ℕ∞ω) ≤ 3 := by exact_mod_cast hj
  rw [heq, fun_iteratedFDeriv_sub_apply ((hfn.mul hgn).of_le hjN).contDiffAt ((hfp.mul hgp).of_le hjN).contDiffAt]
  have hpow : (2 : ℝ) ^ j ≤ 8 := by
    calc
      (2 : ℝ) ^ j ≤ (2 : ℝ) ^ 3 := pow_le_pow_right₀ (by norm_num) hj
      _ = 8 := by norm_num
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (fun z => fn z * gn z) p‖ + ‖iteratedFDeriv ℝ j (fun z => fp z * gp z) p‖ := norm_sub_le _ _
    _ ≤ (2 : ℝ) ^ j * Kpsi * Kphi + (2 : ℝ) ^ j * Kpsi * Kphi := add_le_add hn hp
    _ = (2 * (2 : ℝ) ^ j) * (Kpsi * Kphi) := by ring
    _ ≤ 16 * (Kpsi * Kphi) := mul_le_mul_of_nonneg_right (by linarith only [hpow]) (mul_nonneg hKpsi hKphi)
    _ = _ := by ring

theorem actual_edge_jets_bounded :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j, j ≤ 3 → ∀ p : ℝ × ℝ, ‖iteratedFDeriv ℝ j edge p‖ ≤ C := by
  obtain ⟨Kpsi, hKpsi, hpsi⟩ := psi_iterated_jets_bounded
  let Kphi := 2 * Real.pi + 16
  have hKphi : 0 ≤ Kphi := by dsimp [Kphi]; positivity
  exact ⟨16 * Kpsi * Kphi, by positivity,
    fun j hj p => actual_edge_jets_from_scalar_bounds Kpsi Kphi hKpsi hKphi hpsi phi_iterated_jets_bound p j hj⟩

end
end FangqingSingleLowerEdgeJetBounds
end

section
-- Source component: SingleLowerUniformJets.lean

open scoped BigOperators ContDiff

namespace FangqingSingleLowerUniformJets

open FangqingDisjointBlockBounds FangqingRelayProductBounds

noncomputable section
set_option maxHeartbeats 3500000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def normalizedPair (n : ℕ) (V : Fin (n + 1) → E) (i : Fin n) : E →L[ℝ] (ℝ × ℝ) :=
  (1 / 2 : ℝ) • ((innerSL ℝ (V i.castSucc)).prod (innerSL ℝ (V i.succ)))

theorem normalizedPair_energy (n : ℕ) (V : Fin (n + 1) → E) (hV : Orthonormal ℝ V) (z : E) :
    (∑ i, ‖normalizedPair n V i z‖ ^ 2) ≤ ‖z‖ ^ 2 := by
  have hB : (∑ i, (inner ℝ (V i) z) ^ 2) ≤ ‖z‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using hV.sum_inner_products_le (s := Finset.univ) (x := z)
  have hl : (∑ i : Fin n, (inner ℝ (V i.castSucc) z) ^ 2) ≤ ‖z‖ ^ 2 := by
    have hs := Fin.sum_univ_castSucc (fun i : Fin (n + 1) => (inner ℝ (V i) z) ^ 2)
    have hn := sq_nonneg (inner ℝ (V (Fin.last n)) z)
    linarith only [hB, hs, hn]
  have hr : (∑ i : Fin n, (inner ℝ (V i.succ) z) ^ 2) ≤ ‖z‖ ^ 2 := by
    have hs := Fin.sum_univ_succ (fun i : Fin (n + 1) => (inner ℝ (V i) z) ^ 2)
    have hn := sq_nonneg (inner ℝ (V 0) z)
    linarith only [hB, hs, hn]
  have hp : ∀ i : Fin n, ‖normalizedPair n V i z‖ ^ 2 ≤
      (1 / 2 : ℝ) * ((inner ℝ (V i.castSucc) z) ^ 2 + (inner ℝ (V i.succ) z) ^ 2) := by
    intro i
    let a := inner ℝ (V i.castSucc) z
    let b := inner ℝ (V i.succ) z
    have hm : (max |a| |b|) ^ 2 ≤ a ^ 2 + b ^ 2 := by
      rcases le_total |a| |b| with h | h
      · rw [max_eq_right h, sq_abs]
        nlinarith only [sq_nonneg a]
      · rw [max_eq_left h, sq_abs]
        nlinarith only [sq_nonneg b]
    have heq : ‖normalizedPair n V i z‖ ^ 2 = (1 / 4 : ℝ) * (max |a| |b|) ^ 2 := by
      simp only [normalizedPair, ContinuousLinearMap.smul_apply, ContinuousLinearMap.prod_apply,
        innerSL_apply_apply, norm_smul, Real.norm_eq_abs, Prod.norm_def]
      norm_num
      ring
    rw [heq]
    change (1 / 4 : ℝ) * (max |a| |b|) ^ 2 ≤ (1 / 2 : ℝ) * (a ^ 2 + b ^ 2)
    nlinarith only [hm, sq_nonneg a, sq_nonneg b]
  calc
    _ ≤ ∑ i : Fin n, (1 / 2 : ℝ) *
        ((inner ℝ (V i.castSucc) z) ^ 2 + (inner ℝ (V i.succ) z) ^ 2) :=
      Finset.sum_le_sum (fun i _ => hp i)
    _ = (1 / 2 : ℝ) * ((∑ i : Fin n, (inner ℝ (V i.castSucc) z) ^ 2) +
        (∑ i : Fin n, (inner ℝ (V i.succ) z) ^ 2)) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ _ := by linarith only [hl, hr]

def doublePair : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := (2 : ℝ) • ContinuousLinearMap.id ℝ (ℝ × ℝ)

theorem doublePair_normalizedPair (n : ℕ) (V : Fin (n + 1) → E) (i : Fin n) (z : E) :
    doublePair (normalizedPair n V i z) = (inner ℝ (V i.castSucc) z, inner ℝ (V i.succ) z) := by
  ext <;> simp [doublePair, normalizedPair, innerSL_apply_apply] <;> ring

theorem doublePair_norm_le : ‖doublePair‖ ≤ 2 := by
  apply doublePair.opNorm_le_bound (by norm_num)
  intro p
  simp [doublePair, norm_smul]

theorem iterated_comp_operator_bound
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : Y → ℝ) (P : X →L[ℝ] Y) (hf : ContDiff ℝ 3 f)
    (j : ℕ) (hj : j ≤ 3) (C B : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B) (hP : ‖P‖ ≤ B)
    (x : X) (hlocal : ‖iteratedFDeriv ℝ j f (P x)‖ ≤ C) :
    ‖iteratedFDeriv ℝ j (f ∘ P) x‖ ≤ C * B ^ j := by
  rw [P.iteratedFDeriv_comp_right hf x (by exact_mod_cast hj)]
  have hh := (iteratedFDeriv ℝ j f (P x)).norm_compContinuousLinearMap_le (fun _ => P)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hh
  exact hh.trans (mul_le_mul hlocal (pow_le_pow_left₀ (norm_nonneg P) hP j) (by positivity) hC)

def adjacentSum (n : ℕ) (V : Fin (n + 1) → E) (f : (ℝ × ℝ) → ℝ) (z : E) : ℝ :=
  ∑ i : Fin n, f (inner ℝ (V i.castSucc) z, inner ℝ (V i.succ) z)

theorem adjacentSum_eq_blockSum (n : ℕ) (V : Fin (n + 1) → E) (f : (ℝ × ℝ) → ℝ) :
    adjacentSum n V f = blockSum (normalizedPair n V) (fun _ => f ∘ doublePair) := by
  funext z
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg f (doublePair_normalizedPair n V i z).symm

theorem adjacentSum_contDiff (n : ℕ) (V : Fin (n + 1) → E) (f : (ℝ × ℝ) → ℝ)
    (hf : ContDiff ℝ 3 f) : ContDiff ℝ 3 (adjacentSum n V f) := by
  rw [adjacentSum_eq_blockSum]
  exact ContDiff.sum (fun i _ => (hf.comp doublePair.contDiff).comp (normalizedPair n V i).contDiff)

theorem adjacentSum_second_bound (n : ℕ) (V : Fin (n + 1) → E) (hV : Orthonormal ℝ V)
    (f : (ℝ × ℝ) → ℝ) (hf : ContDiff ℝ 3 f) (C : ℝ) (hC : 0 ≤ C)
    (hlocal : ∀ p, ‖iteratedFDeriv ℝ 2 f p‖ ≤ C) (x : E) :
    ‖iteratedFDeriv ℝ 2 (adjacentSum n V f) x‖ ≤ 4 * C := by
  rw [adjacentSum_eq_blockSum]
  apply second_blockSum_bound (normalizedPair n V) (fun _ => f ∘ doublePair)
    (fun _ => hf.comp doublePair.contDiff) (normalizedPair_energy n V hV) (4 * C) (by positivity) x
  intro i
  convert iterated_comp_operator_bound f doublePair hf 2 (by omega) C 2 hC (by norm_num)
    doublePair_norm_le (normalizedPair n V i x) (hlocal _) using 1 <;> ring

theorem adjacentSum_third_bound (n : ℕ) (V : Fin (n + 1) → E) (hV : Orthonormal ℝ V)
    (f : (ℝ × ℝ) → ℝ) (hf : ContDiff ℝ 3 f) (C : ℝ) (hC : 0 ≤ C)
    (hlocal : ∀ p, ‖iteratedFDeriv ℝ 3 f p‖ ≤ C) (x : E) :
    ‖iteratedFDeriv ℝ 3 (adjacentSum n V f) x‖ ≤ 8 * C := by
  rw [adjacentSum_eq_blockSum]
  apply third_blockSum_bound (normalizedPair n V) (fun _ => f ∘ doublePair)
    (fun _ => hf.comp doublePair.contDiff) (normalizedPair_energy n V hV) (8 * C) (by positivity) x
  intro i
  convert iterated_comp_operator_bound f doublePair hf 3 (by omega) C 2 hC (by norm_num)
    doublePair_norm_le (normalizedPair n V i x) (hlocal _) using 1 <;> ring


section GeneralFirstBlock
variable {I X Y : Type*} [Fintype I]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem sum_projection_norm_bound (P : I → X →L[ℝ] Y)
    (henergy : ∀ v : X, (∑ i, ‖P i v‖ ^ 2) ≤ ‖v‖ ^ 2) (v : X) :
    (∑ i, ‖P i v‖) ≤ Real.sqrt (Fintype.card I) * ‖v‖ := by
  have hh := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ : I => (1 : ℝ)) (fun i => ‖P i v‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hh
  have hr : Real.sqrt (∑ i, ‖P i v‖ ^ 2) ≤ ‖v‖ :=
    (Real.sqrt_le_sqrt (henergy v)).trans_eq (Real.sqrt_sq (norm_nonneg v))
  exact hh.trans (mul_le_mul_of_nonneg_left hr (Real.sqrt_nonneg _))

theorem first_blockSum_bound (P : I → X →L[ℝ] Y) (f : I → Y → ℝ)
    (hf : ∀ i, ContDiff ℝ 3 (f i))
    (henergy : ∀ v : X, (∑ i, ‖P i v‖ ^ 2) ≤ ‖v‖ ^ 2)
    (C : ℝ) (hC : 0 ≤ C) (x : X)
    (hlocal : ∀ i, ‖iteratedFDeriv ℝ 1 (f i) (P i x)‖ ≤ C) :
    ‖iteratedFDeriv ℝ 1 (blockSum P f) x‖ ≤ C * Real.sqrt (Fintype.card I) := by
  apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg hC (Real.sqrt_nonneg _))
  intro v
  rw [blockSum_iterated_apply P f 3 hf 1 (by norm_num)]
  calc
    _ ≤ ∑ i, ‖iteratedFDeriv ℝ 1 (f i) (P i x) (fun k => P i (v k))‖ := norm_sum_le _ _
    _ ≤ ∑ i, C * ‖P i (v 0)‖ := by
      apply Finset.sum_le_sum
      intro i _
      have hh := (iteratedFDeriv ℝ 1 (f i) (P i x)).le_opNorm (fun k => P i (v k))
      simp only [Fin.prod_univ_one] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right (hlocal i) (norm_nonneg _))
    _ = C * (∑ i, ‖P i (v 0)‖) := by rw [Finset.mul_sum]
    _ ≤ C * (Real.sqrt (Fintype.card I) * ‖v 0‖) :=
      mul_le_mul_of_nonneg_left (sum_projection_norm_bound P henergy (v 0)) hC
    _ = (C * Real.sqrt (Fintype.card I)) * ∏ k, ‖v k‖ := by rw [Fin.prod_univ_one]; ring

end GeneralFirstBlock

theorem adjacentSum_first_bound (n : ℕ) (V : Fin (n + 1) → E) (hV : Orthonormal ℝ V)
    (f : (ℝ × ℝ) → ℝ) (hf : ContDiff ℝ 3 f) (C : ℝ) (hC : 0 ≤ C)
    (hlocal : ∀ p, ‖iteratedFDeriv ℝ 1 f p‖ ≤ C) (x : E) :
    ‖iteratedFDeriv ℝ 1 (adjacentSum n V f) x‖ ≤ 2 * C * Real.sqrt n := by
  rw [adjacentSum_eq_blockSum]
  have hb : ‖iteratedFDeriv ℝ 1 (blockSum (normalizedPair n V) (fun _ => f ∘ doublePair)) x‖ ≤
      2 * C * Real.sqrt (Fintype.card (Fin n)) := by
    apply first_blockSum_bound (normalizedPair n V) (fun _ => f ∘ doublePair)
      (fun _ => hf.comp doublePair.contDiff) (normalizedPair_energy n V hV) (2 * C) (by positivity) x
    intro i
    convert iterated_comp_operator_bound f doublePair hf 1 (by omega) C 2 hC (by norm_num)
      doublePair_norm_le (normalizedPair n V i x) (hlocal _) using 1 <;> ring
  simpa only [Fintype.card_fin] using hb

end
end FangqingSingleLowerUniformJets
end

section
-- Source component: SingleLowerPhysicalJetBounds.lean

open scoped BigOperators ContDiff

namespace FangqingSingleLowerPhysicalJetBounds

open FangqingSingleLowerScalarProfiles FangqingSingleLowerChainEdge
  FangqingSingleLowerRobustChain FangqingSingleLowerPhysicalGradient
  FangqingSingleLowerScalarJetBounds FangqingSingleLowerEdgeJetBounds
  FangqingSingleLowerUniformJets FangqingRelayProductBounds

noncomputable section
set_option maxHeartbeats 3500000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem physicalChain_decomposition (n : ℕ) (V : Fin (n + 1) → E) :
    physicalChain n V = fun x => -phi (inner ℝ (V 0) x) + adjacentSum n V edge x := by
  funext x
  simp only [physicalChain, chain, adjacentSum]

theorem seed_jet_bound (n : ℕ) (V : Fin (n + 1) → E) (hV : Orthonormal ℝ V)
    (x : E) (j : ℕ) (hj : j ≤ 3) :
    ‖iteratedFDeriv ℝ j (fun y : E => -phi (inner ℝ (V 0) y)) x‖ ≤ 2 * Real.pi + 16 := by
  let P := innerSL ℝ (V 0)
  have hP : ‖P‖ ≤ 1 := by
    dsimp only [P]
    rw [innerSL_apply_norm, hV.norm_eq_one 0]
  change ‖iteratedFDeriv ℝ j (-(phi ∘ P)) x‖ ≤ _
  rw [iteratedFDeriv_neg_apply, norm_neg]
  exact (norm_iterated_comp_contraction phi P 3 (phi_smooth.of_le (by decide)) hP x j (by exact_mod_cast hj)).trans
    (phi_iterated_jets_bound j hj (P x))

theorem seed_contDiff (n : ℕ) (V : Fin (n + 1) → E) :
    ContDiff ℝ 3 (fun y : E => -phi (inner ℝ (V 0) y)) :=
  ((phi_smooth.of_le (by decide)).comp (innerSL ℝ (V 0)).contDiff).neg

theorem physicalChain_first_bound (C : ℝ) (hC : 0 ≤ C)
    (hEdge : ∀ p, ‖iteratedFDeriv ℝ 1 edge p‖ ≤ C)
    (n : ℕ) (V : Fin (n + 1) → E) (hV : Orthonormal ℝ V) (x : E) :
    ‖iteratedFDeriv ℝ 1 (physicalChain n V) x‖ ≤
      (2 * Real.pi + 16 + 2 * C) * Real.sqrt ((n + 1 : ℕ) : ℝ) := by
  have hAdj := adjacentSum_first_bound n V hV edge (edge_smooth.of_le (by decide)) C hC hEdge x
  have hSeed := seed_jet_bound n V hV x 1 (by omega)
  have hcont := adjacentSum_contDiff n V edge (edge_smooth.of_le (by decide))
  have hbound : ‖iteratedFDeriv ℝ 1 (physicalChain n V) x‖ ≤ (2 * Real.pi + 16) + 2 * C * Real.sqrt n := by
    rw [physicalChain_decomposition, fun_iteratedFDeriv_add_apply ((seed_contDiff n V).of_le (by norm_num : (1 : ℕ∞ω) ≤ 3)).contDiffAt (hcont.of_le (by norm_num : (1 : ℕ∞ω) ≤ 3)).contDiffAt]
    exact (norm_add_le _ _).trans (add_le_add hSeed hAdj)
  have hs : (1 : ℝ) ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) :=
    Real.one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ n + 1 by omega))
  have hsn : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast (Nat.le_succ n))
  have hK : 0 ≤ 2 * Real.pi + 16 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hs hK
  have h2 := mul_le_mul_of_nonneg_left hsn (by positivity : 0 ≤ 2 * C)
  nlinarith only [hbound, h1, h2]

theorem physicalChain_second_bound (C : ℝ) (hC : 0 ≤ C)
    (hEdge : ∀ p, ‖iteratedFDeriv ℝ 2 edge p‖ ≤ C)
    (n : ℕ) (V : Fin (n + 1) → E) (hV : Orthonormal ℝ V) (x : E) :
    ‖iteratedFDeriv ℝ 2 (physicalChain n V) x‖ ≤ 2 * Real.pi + 16 + 4 * C := by
  have hAdj := adjacentSum_second_bound n V hV edge (edge_smooth.of_le (by decide)) C hC hEdge x
  have hSeed := seed_jet_bound n V hV x 2 (by omega)
  have hcont := adjacentSum_contDiff n V edge (edge_smooth.of_le (by decide))
  rw [physicalChain_decomposition, fun_iteratedFDeriv_add_apply ((seed_contDiff n V).of_le (by norm_num : (2 : ℕ∞ω) ≤ 3)).contDiffAt (hcont.of_le (by norm_num : (2 : ℕ∞ω) ≤ 3)).contDiffAt]
  exact (norm_add_le _ _).trans (add_le_add hSeed hAdj)

theorem physicalChain_third_bound (C : ℝ) (hC : 0 ≤ C)
    (hEdge : ∀ p, ‖iteratedFDeriv ℝ 3 edge p‖ ≤ C)
    (n : ℕ) (V : Fin (n + 1) → E) (hV : Orthonormal ℝ V) (x : E) :
    ‖iteratedFDeriv ℝ 3 (physicalChain n V) x‖ ≤ 2 * Real.pi + 16 + 8 * C := by
  have hAdj := adjacentSum_third_bound n V hV edge (edge_smooth.of_le (by decide)) C hC hEdge x
  have hSeed := seed_jet_bound n V hV x 3 (by omega)
  have hcont := adjacentSum_contDiff n V edge (edge_smooth.of_le (by decide))
  rw [physicalChain_decomposition, fun_iteratedFDeriv_add_apply (seed_contDiff n V).contDiffAt hcont.contDiffAt]
  exact (norm_add_le _ _).trans (add_le_add hSeed hAdj)

universe u

/-- One fixed numerical bound precedes every ambient Hilbert space, chain
    length and orthonormal orientation.  Local scalar bounds above are proved
    for the actual psi/Phi profiles, not additional hypotheses here. -/
theorem universal_actual_physical_chain_jets :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (F : Type u) [NormedAddCommGroup F] [InnerProductSpace ℝ F],
      ∀ (n : ℕ) (V : Fin (n + 1) → F), Orthonormal ℝ V → ∀ x : F,
        ‖iteratedFDeriv ℝ 1 (physicalChain n V) x‖ ≤ C * Real.sqrt ((n + 1 : ℕ) : ℝ) ∧
        ‖iteratedFDeriv ℝ 2 (physicalChain n V) x‖ ≤ C ∧
        ‖iteratedFDeriv ℝ 3 (physicalChain n V) x‖ ≤ C := by
  obtain ⟨B, hB, hBound⟩ := actual_edge_jets_bounded
  let C := 1 + (2 * Real.pi + 16) + 8 * B
  have hC : 1 ≤ C := by dsimp [C]; have := Real.pi_pos; linarith only [hB, this]
  refine ⟨C, hC, ?_⟩
  intro F inst inst' n V hV x
  have h1 := physicalChain_first_bound B hB (hBound 1 (by omega)) n V hV x
  have h2 := physicalChain_second_bound B hB (hBound 2 (by omega)) n V hV x
  have h3 := physicalChain_third_bound B hB (hBound 3 (by omega)) n V hV x
  have hc1 : 2 * Real.pi + 16 + 2 * B ≤ C := by dsimp [C]; linarith only [hB]
  have hc2 : 2 * Real.pi + 16 + 4 * B ≤ C := by dsimp [C]; linarith only [hB]
  have hc3 : 2 * Real.pi + 16 + 8 * B ≤ C := by dsimp [C]; linarith
  exact ⟨h1.trans (mul_le_mul_of_nonneg_right hc1 (Real.sqrt_nonneg _)), h2.trans hc2, h3.trans hc3⟩

end
end FangqingSingleLowerPhysicalJetBounds
end

section
-- Source component: SingleLowerExteriorGradient.lean

open scoped BigOperators ContDiff

namespace FangqingSingleLowerExteriorGradient

open FangqingSingleLowerRobustChain FangqingSingleLowerPhysicalGradient
  FangqingSingleLowerPhysicalJetBounds FangqingSingleLowerLocalizedGap
  FangqingRelayProductBounds FangqingRadialGateBounds

noncomputable section
set_option maxHeartbeats 4500000

theorem first_product_jet_bound
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f g : X → ℝ) (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g) (x : X)
    (a0 a1 b0 b1 : ℝ) (hA0 : ‖f x‖ ≤ a0) (hA1 : ‖iteratedFDeriv ℝ 1 f x‖ ≤ a1)
    (hB0 : ‖g x‖ ≤ b0) (hB1 : ‖iteratedFDeriv ℝ 1 g x‖ ≤ b1) :
    ‖iteratedFDeriv ℝ 1 (fun y => f y * g y) x‖ ≤ a0 * b1 + a1 * b0 := by
  have hA : ∀ i, i ≤ 1 → ‖iteratedFDeriv ℝ i f x‖ ≤ budget a0 a1 0 0 i := by
    intro i hi
    interval_cases i
    · simpa only [budget, norm_iteratedFDeriv_zero] using hA0
    · simpa only [budget] using hA1
  have hB : ∀ i, i ≤ 1 → ‖iteratedFDeriv ℝ i g x‖ ≤ budget b0 b1 0 0 i := by
    intro i hi
    interval_cases i
    · simpa only [budget, norm_iteratedFDeriv_zero] using hB0
    · simpa only [budget] using hB1
  have hp := product_iterated_bound f g 3 hf hg x 1 (by norm_num)
    (budget a0 a1 0 0) (budget b0 b1 0 0) hA hB
  simpa [budget, Finset.sum_range_succ] using hp

def radiusConstant (C K : ℝ) : ℝ := 20 * (1 + C + K * (4 * Real.pi))
def chainRadius (n : ℕ) (C K : ℝ) : ℝ := radiusConstant C K * Real.sqrt ((n + 1 : ℕ) : ℝ)

theorem radiusConstant_ge_one (C K : ℝ) (hC : 1 ≤ C) (hK : 0 ≤ K) : 1 ≤ radiusConstant C K := by
  have h := mul_nonneg hK (by positivity : 0 ≤ 4 * Real.pi)
  dsimp only [radiusConstant]
  linarith only [hC, h]

theorem chainRadius_positive (n : ℕ) (C K : ℝ) (hC : 1 ≤ C) (hK : 0 ≤ K) : 0 < chainRadius n C K := by
  have hc : 0 < radiusConstant C K := zero_lt_one.trans_le (radiusConstant_ge_one C K hC hK)
  have ht : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n + 1 by omega)
  exact mul_pos hc (Real.sqrt_pos.mpr ht)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem cutoff_contDiff (theta : ℝ → ℝ) (htheta : ContDiff ℝ 3 theta) (R : ℝ) :
    ContDiff ℝ 3 (scaledGate theta R (0 : E)) := by
  exact htheta.comp (((contDiff_id.sub contDiff_const).norm_sq ℝ).div_const (R ^ 2))

theorem actual_chain_value_bound (n : ℕ) (V : Fin (n + 1) → E) (x : E) :
    ‖physicalChain n V x‖ ≤ (4 * Real.pi) * ((n + 1 : ℕ) : ℝ) := by
  simpa only [physicalChain, Real.norm_eq_abs, Nat.cast_add, Nat.cast_one] using
    chain_abs_bound n (fun i => inner ℝ (V i) x)

theorem cutoff_chain_first_bound
    (theta : ℝ → ℝ) (htheta : ContDiff ℝ 3 theta) (hrange : ∀ t, 0 ≤ theta t ∧ theta t ≤ 1)
    (C K : ℝ) (hC : 1 ≤ C) (hK : 0 ≤ K) (n : ℕ) (V : Fin (n + 1) → E) (x : E)
    (hChain : ‖iteratedFDeriv ℝ 1 (physicalChain n V) x‖ ≤ C * Real.sqrt ((n + 1 : ℕ) : ℝ))
    (hGate : ‖iteratedFDeriv ℝ 1 (scaledGate theta (chainRadius n C K) (0 : E)) x‖ ≤ K / chainRadius n C K) :
    ‖iteratedFDeriv ℝ 1 (fun y => scaledGate theta (chainRadius n C K) (0 : E) y * physicalChain n V y) x‖ ≤
      (C + K * (4 * Real.pi)) * Real.sqrt ((n + 1 : ℕ) : ℝ) := by
  let T : ℝ := ((n + 1 : ℕ) : ℝ)
  let s := Real.sqrt T
  let R := chainRadius n C K
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hR : 0 < R := chainRadius_positive n C K hC hK
  have hs : s ^ 2 = T := Real.sq_sqrt hT
  have hCR : 1 ≤ radiusConstant C K := radiusConstant_ge_one C K hC hK
  have hTR : T / R ≤ s := by
    apply (div_le_iff₀ hR).mpr
    change T ≤ s * (radiusConstant C K * s)
    have hm := mul_le_mul_of_nonneg_right hCR (sq_nonneg s)
    nlinarith only [hm, hs]
  have h0 : ‖scaledGate theta R (0 : E) x‖ ≤ 1 := by
    have ht := hrange (‖x‖ ^ 2 / R ^ 2)
    simpa only [scaledGate, sub_zero, Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2
  have hg : ContDiff ℝ 3 (physicalChain n V) := (physicalChain_smooth n V).of_le (by decide)
  have hp := first_product_jet_bound (scaledGate theta R (0 : E)) (physicalChain n V)
    (cutoff_contDiff theta htheta R) hg x 1 (K / R) ((4 * Real.pi) * T) (C * s)
    h0 hGate (actual_chain_value_bound n V x) hChain
  have hm : (K / R) * ((4 * Real.pi) * T) ≤ (K * (4 * Real.pi)) * s := by
    calc
      _ = (K * (4 * Real.pi)) * (T / R) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hTR (mul_nonneg hK (by positivity))
  dsimp only [T, s, R] at hp hm
  nlinarith only [hp, hm]

theorem quadratic_first_norm (x : E) :
    ‖(1 / 20 : ℝ) • (2 • innerSL ℝ x)‖ = (1 / 10 : ℝ) * ‖x‖ := by
  rw [← Nat.cast_smul_eq_nsmul ℝ 2]
  simp only [norm_smul, Real.norm_eq_abs, innerSL_apply_norm]
  norm_num
  ring

theorem actual_localized_exterior_lower_from_bounds
    (theta : ℝ → ℝ) (htheta : ContDiff ℝ 3 theta) (hrange : ∀ t, 0 ≤ theta t ∧ theta t ≤ 1)
    (C K : ℝ) (hC : 1 ≤ C) (hK : 0 ≤ K) (n : ℕ) (V : Fin (n + 1) → E) (x : E)
    (hChain : ‖iteratedFDeriv ℝ 1 (physicalChain n V) x‖ ≤ C * Real.sqrt ((n + 1 : ℕ) : ℝ))
    (hGate : ‖iteratedFDeriv ℝ 1 (scaledGate theta (chainRadius n C K) (0 : E)) x‖ ≤ K / chainRadius n C K)
    (hx : (3 / 2 : ℝ) * chainRadius n C K ≤ ‖x‖) :
    1 ≤ ‖fderiv ℝ (localizedChain theta (chainRadius n C K) n V) x‖ := by
  let s := Real.sqrt (((n + 1 : ℕ) : ℝ))
  let R := chainRadius n C K
  let p := fun y : E => scaledGate theta R (0 : E) y * physicalChain n V y
  let qd := (1 / 20 : ℝ) • (2 • innerSL ℝ x)
  have hpcont : ContDiff ℝ 3 p :=
    (cutoff_contDiff theta htheta R).mul ((physicalChain_smooth n V).of_le (by decide))
  have hp := (hpcont.differentiable (by norm_num) x).hasFDerivAt
  have hq : HasFDerivAt (fun y : E => (1 / 20 : ℝ) * ‖y‖ ^ 2) qd x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (1 / 20 : ℝ)
  have hfun : (fun y : E => p y + (1 / 20 : ℝ) * ‖y‖ ^ 2) = localizedChain theta R n V := by
    funext y
    simp only [p, localizedChain, scaledGate, sub_zero]
  have hD : fderiv ℝ (localizedChain theta R n V) x = fderiv ℝ p x + qd := by
    rw [← hfun]
    exact (hp.add hq).fderiv
  have htri : (1 / 10 : ℝ) * ‖x‖ ≤ ‖fderiv ℝ (localizedChain theta R n V) x‖ + ‖fderiv ℝ p x‖ := by
    rw [← quadratic_first_norm x, hD]
    have hh := norm_sub_le (fderiv ℝ p x + qd) (fderiv ℝ p x)
    have heq : (fderiv ℝ p x + qd) - fderiv ℝ p x = qd := by abel
    simpa only [heq] using hh
  have hProd := cutoff_chain_first_bound theta htheta hrange C K hC hK n V x hChain hGate
  rw [norm_iteratedFDeriv_one] at hProd
  change ‖fderiv ℝ p x‖ ≤ (C + K * (4 * Real.pi)) * s at hProd
  have hs : 1 ≤ s := Real.one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ n + 1 by omega))
  have hOuter : 3 * (1 + C + K * (4 * Real.pi)) * s ≤ (1 / 10 : ℝ) * ‖x‖ := by
    have hh := mul_le_mul_of_nonneg_left hx (by norm_num : (0 : ℝ) ≤ 1 / 10)
    change (1 / 10 : ℝ) * ((3 / 2 : ℝ) * (radiusConstant C K * s)) ≤ (1 / 10 : ℝ) * ‖x‖ at hh
    dsimp only [radiusConstant] at hh
    nlinarith only [hh]
  have hExtra : 0 ≤ (C + K * (4 * Real.pi)) * s :=
    mul_nonneg (add_nonneg (zero_le_one.trans hC) (mul_nonneg hK (by positivity))) (zero_le_one.trans hs)
  change 1 ≤ ‖fderiv ℝ (localizedChain theta R n V) x‖
  nlinarith only [htri, hProd, hOuter, hExtra, hs]

universe u

theorem universal_actual_localized_exterior_gradient :
    ∃ CR : ℝ, 1 ≤ CR ∧ ∀ (F : Type u) [NormedAddCommGroup F] [InnerProductSpace ℝ F],
      ∀ (n : ℕ) (V : Fin (n + 1) → F), Orthonormal ℝ V → ∀ x : F,
      let R := CR * Real.sqrt ((n + 1 : ℕ) : ℝ)
      (3 / 2 : ℝ) * R ≤ ‖x‖ →
        1 ≤ ‖fderiv ℝ (localizedChain FangqingPublicShellProfiles.theta R n V) x‖ := by
  obtain ⟨C, hC, hChain⟩ := universal_actual_physical_chain_jets.{u}
  obtain ⟨K, hK, hGate⟩ := universal_three_gate_bounds.{u} FangqingPublicShellProfiles.theta 2 (by norm_num)
    (FangqingPublicShellProfiles.theta_smooth.of_le (by decide))
    (fun t ht => FangqingPublicShellProfiles.theta_one t (by linarith only [ht]))
    (fun t ht => FangqingPublicShellProfiles.theta_zero t (by nlinarith only [ht]))
  refine ⟨radiusConstant C K, radiusConstant_ge_one C K hC hK, ?_⟩
  intro F inst inst' n V hV x R hx
  apply actual_localized_exterior_lower_from_bounds FangqingPublicShellProfiles.theta
    (FangqingPublicShellProfiles.theta_smooth.of_le (by decide)) FangqingPublicShellProfiles.theta_range
    C K hC hK n V x (hChain F n V hV x).1 ?_ hx
  simpa only [pow_one] using hGate F (chainRadius n C K) (chainRadius_positive n C K hC hK) (0 : F) x 1 (by omega) (by omega)

end
end FangqingSingleLowerExteriorGradient
end

section
-- Source component: SingleLowerLocalizedJetBounds.lean

open scoped BigOperators ContDiff NNReal

namespace FangqingSingleLowerLocalizedJetBounds

open FangqingSingleLowerPhysicalGradient FangqingSingleLowerPhysicalJetBounds
  FangqingSingleLowerLocalizedGap FangqingSingleLowerExteriorGradient
  FangqingRelayProductBounds FangqingRadialGateBounds FangqingJetToRegularity

noncomputable section
set_option maxHeartbeats 4500000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def quadratic (x : E) : ℝ := (1 / 20 : ℝ) * ‖x‖ ^ 2

theorem quadratic_fderiv (x : E) :
    fderiv ℝ (quadratic : E → ℝ) x = ((1 / 10 : ℝ) • innerSL ℝ) x := by
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (1 / 20 : ℝ)
  change fderiv ℝ (fun y : E => (1 / 20 : ℝ) * ‖y‖ ^ 2) x = _
  rw [h.fderiv]
  ext v
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
  ring

theorem quadratic_second_bound (x : E) : ‖iteratedFDeriv ℝ 2 (quadratic : E → ℝ) x‖ ≤ 1 := by
  let L : E →L[ℝ] (E →L[ℝ] ℝ) := (1 / 10 : ℝ) • innerSL ℝ
  have hfun : fderiv ℝ (quadratic : E → ℝ) = fun y => L y := funext quadratic_fderiv
  rw [← norm_iteratedFDeriv_fderiv, hfun, norm_iteratedFDeriv_one, L.fderiv]
  have hn : ‖L‖ ≤ (1 / 10 : ℝ) := by
    apply L.opNorm_le_bound (by norm_num)
    intro v
    change ‖(1 / 10 : ℝ) • innerSL ℝ v‖ ≤ (1 / 10 : ℝ) * ‖v‖
    rw [norm_smul, Real.norm_eq_abs, innerSL_apply_norm]
    norm_num
  exact hn.trans (by norm_num)

theorem quadratic_third_bound (x : E) : ‖iteratedFDeriv ℝ 3 (quadratic : E → ℝ) x‖ ≤ 1 := by
  let L : E →L[ℝ] (E →L[ℝ] ℝ) := (1 / 10 : ℝ) • innerSL ℝ
  have hfun : fderiv ℝ (quadratic : E → ℝ) = fun y => L y := funext quadratic_fderiv
  have hL : fderiv ℝ (fun y => L y) = fun _ => L := funext (fun x => L.fderiv)
  rw [← norm_iteratedFDeriv_fderiv, hfun, ← norm_iteratedFDeriv_fderiv, hL, iteratedFDeriv_succ_const]
  norm_num

theorem reciprocal_radius_bounds (s R : ℝ) (hs : 1 ≤ s) (hR : s ≤ R) :
    s / R ≤ 1 ∧ s ^ 2 / R ^ 2 ≤ 1 ∧ 1 / R ≤ 1 ∧ s / R ^ 2 ≤ 1 ∧ s ^ 2 / R ^ 3 ≤ 1 := by
  have hR1 : 1 ≤ R := hs.trans hR
  have hR0 : 0 < R := zero_lt_one.trans_le hR1
  have hR2 : R ≤ R ^ 2 := by nlinarith only [hR1, sq_nonneg (R - 1)]
  have hR3 : R ^ 2 ≤ R ^ 3 := by
    have hh := mul_le_mul_of_nonneg_right hR1 (sq_nonneg R)
    nlinarith only [hh]
  have hs2 : s ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (zero_le_one.trans hs) hR 2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (div_le_iff₀ hR0).mpr (by simpa only [one_mul] using hR)
  · exact (div_le_iff₀ (pow_pos hR0 2)).mpr (by simpa only [one_mul] using hs2)
  · exact (div_le_iff₀ hR0).mpr (by simpa only [one_mul] using hR1)
  · exact (div_le_iff₀ (pow_pos hR0 2)).mpr (by simpa only [one_mul] using hR.trans hR2)
  · exact (div_le_iff₀ (pow_pos hR0 3)).mpr (by simpa only [one_mul] using hs2.trans hR3)

theorem localized_product_high_jet_bounds
    (f g : E → ℝ) (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    (C0 C K s R : ℝ) (hC0 : 0 ≤ C0) (hC : 0 ≤ C) (hK : 0 ≤ K) (hs : 1 ≤ s) (hR : s ≤ R)
    (x : E) (hf0 : ‖f x‖ ≤ 1)
    (hf1 : ‖iteratedFDeriv ℝ 1 f x‖ ≤ K / R)
    (hf2 : ‖iteratedFDeriv ℝ 2 f x‖ ≤ K / R ^ 2)
    (hf3 : ‖iteratedFDeriv ℝ 3 f x‖ ≤ K / R ^ 3)
    (hg0 : ‖g x‖ ≤ C0 * s ^ 2) (hg1 : ‖iteratedFDeriv ℝ 1 g x‖ ≤ C * s)
    (hg2 : ‖iteratedFDeriv ℝ 2 g x‖ ≤ C) (hg3 : ‖iteratedFDeriv ℝ 3 g x‖ ≤ C) :
    ‖iteratedFDeriv ℝ 2 (fun y => f y * g y) x‖ ≤ C + 2 * K * C + K * C0 ∧
    ‖iteratedFDeriv ℝ 3 (fun y => f y * g y) x‖ ≤ C + 6 * K * C + K * C0 := by
  obtain ⟨hr1, hr2, hr3, hr4, hr5⟩ := reciprocal_radius_bounds s R hs hR
  have ht1 : 2 * (K / R) * (C * s) ≤ 2 * K * C := by
    calc
      _ = (2 * K * C) * (s / R) := by ring
      _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hr1 (by positivity : 0 ≤ 2 * K * C)
  have ht2 : (K / R ^ 2) * (C0 * s ^ 2) ≤ K * C0 := by
    calc
      _ = (K * C0) * (s ^ 2 / R ^ 2) := by ring
      _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hr2 (mul_nonneg hK hC0)
  have ht3 : 3 * (K / R) * C ≤ 3 * K * C := by
    calc
      _ = (3 * K * C) * (1 / R) := by ring
      _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hr3 (by positivity : 0 ≤ 3 * K * C)
  have ht4 : 3 * (K / R ^ 2) * (C * s) ≤ 3 * K * C := by
    calc
      _ = (3 * K * C) * (s / R ^ 2) := by ring
      _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hr4 (by positivity : 0 ≤ 3 * K * C)
  have ht5 : (K / R ^ 3) * (C0 * s ^ 2) ≤ K * C0 := by
    calc
      _ = (K * C0) * (s ^ 2 / R ^ 3) := by ring
      _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hr5 (mul_nonneg hK hC0)
  have h2 := product_second_bound f g hf hg x 1 (K / R) (K / R ^ 2) (C0 * s ^ 2) (C * s) C
    hf0 hf1 hf2 hg0 hg1 hg2
  have h3 := product_third_bound f g hf hg x 1 (K / R) (K / R ^ 2) (K / R ^ 3)
    (C0 * s ^ 2) (C * s) C C hf0 hf1 hf2 hf3 hg0 hg1 hg2 hg3
  constructor <;> nlinarith only [h2, h3, ht1, ht2, ht3, ht4, ht5]

def secondConstant (C K : ℝ) : ℝ := C + 2 * K * C + K * (4 * Real.pi) + 1
def thirdConstant (C K : ℝ) : ℝ := C + 6 * K * C + K * (4 * Real.pi) + 1

theorem actual_localized_high_jets_from_bounds
    (theta : ℝ → ℝ) (htheta : ContDiff ℝ 3 theta) (hrange : ∀ t, 0 ≤ theta t ∧ theta t ≤ 1)
    (C K : ℝ) (hC : 1 ≤ C) (hK : 0 ≤ K) (n : ℕ) (V : Fin (n + 1) → E) (x : E)
    (hChain : ‖iteratedFDeriv ℝ 1 (physicalChain n V) x‖ ≤ C * Real.sqrt ((n + 1 : ℕ) : ℝ) ∧
      ‖iteratedFDeriv ℝ 2 (physicalChain n V) x‖ ≤ C ∧ ‖iteratedFDeriv ℝ 3 (physicalChain n V) x‖ ≤ C)
    (hGate : ∀ j, 1 ≤ j → j ≤ 3 →
      ‖iteratedFDeriv ℝ j (scaledGate theta (chainRadius n C K) (0 : E)) x‖ ≤ K / chainRadius n C K ^ j) :
    ‖iteratedFDeriv ℝ 2 (localizedChain theta (chainRadius n C K) n V) x‖ ≤ secondConstant C K ∧
    ‖iteratedFDeriv ℝ 3 (localizedChain theta (chainRadius n C K) n V) x‖ ≤ thirdConstant C K := by
  let s := Real.sqrt (((n + 1 : ℕ) : ℝ))
  let R := chainRadius n C K
  let f := scaledGate theta R (0 : E)
  let g := physicalChain n V
  have hs : 1 ≤ s := Real.one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ n + 1 by omega))
  have hRs : s ≤ R := by
    change s ≤ radiusConstant C K * s
    have hm := mul_nonneg (sub_nonneg.mpr (radiusConstant_ge_one C K hC hK)) (zero_le_one.trans hs)
    nlinarith only [hm]
  have hf : ContDiff ℝ 3 f := cutoff_contDiff theta htheta R
  have hg : ContDiff ℝ 3 g := (physicalChain_smooth n V).of_le (by decide)
  have h0 : ‖f x‖ ≤ 1 := by
    have ht := hrange (‖x‖ ^ 2 / R ^ 2)
    simpa only [f, scaledGate, sub_zero, Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2
  have hg0 : ‖g x‖ ≤ (4 * Real.pi) * s ^ 2 := by
    simpa only [g, s, Real.sq_sqrt (Nat.cast_nonneg (n + 1))] using actual_chain_value_bound n V x
  have hb := localized_product_high_jet_bounds f g hf hg (4 * Real.pi) C K s R (by positivity)
    (zero_le_one.trans hC) hK hs hRs x h0
    (by simpa only [pow_one] using hGate 1 (by omega) (by omega))
    (hGate 2 (by omega) (by omega)) (hGate 3 (by omega) (by omega)) hg0 hChain.1 hChain.2.1 hChain.2.2
  have hq : ContDiff ℝ 3 (quadratic : E → ℝ) := contDiff_const.mul (contDiff_id.norm_sq ℝ)
  have hfun : localizedChain theta R n V = fun y => (f y * g y) + quadratic y := by
    funext y
    simp only [localizedChain, f, g, scaledGate, sub_zero, quadratic]
  constructor
  · rw [hfun, fun_iteratedFDeriv_add_apply ((hf.mul hg).of_le (by norm_num : (2 : ℕ∞ω) ≤ 3)).contDiffAt
      (hq.of_le (by norm_num : (2 : ℕ∞ω) ≤ 3)).contDiffAt]
    exact (norm_add_le _ _).trans (by simpa only [secondConstant] using add_le_add hb.1 (quadratic_second_bound x))
  · rw [hfun, fun_iteratedFDeriv_add_apply (hf.mul hg).contDiffAt hq.contDiffAt]
    exact (norm_add_le _ _).trans (by simpa only [thirdConstant] using add_le_add hb.2 (quadratic_third_bound x))

universe u

theorem universal_actual_localized_chain_class :
    ∃ CR C2 C3 : ℝ, 1 ≤ CR ∧ 1 ≤ C2 ∧ 1 ≤ C3 ∧
      ∀ (F : Type u) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F],
      ∀ (n : ℕ) (V : Fin (n + 1) → F), Orthonormal ℝ V →
      let R := CR * Real.sqrt ((n + 1 : ℕ) : ℝ)
      let f := localizedChain FangqingPublicShellProfiles.theta R n V
      ContDiff ℝ ∞ f ∧
      (∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C2) ∧
      (∀ x y, ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤ C3 * ‖x - y‖) ∧
      (∀ x, (3 / 2 : ℝ) * R ≤ ‖x‖ → 1 ≤ ‖fderiv ℝ f x‖) := by
  obtain ⟨C, hC, hChain⟩ := universal_actual_physical_chain_jets.{u}
  obtain ⟨K, hK, hGate⟩ := universal_three_gate_bounds.{u} FangqingPublicShellProfiles.theta 2 (by norm_num)
    (FangqingPublicShellProfiles.theta_smooth.of_le (by decide))
    (fun t ht => FangqingPublicShellProfiles.theta_one t (by linarith only [ht]))
    (fun t ht => FangqingPublicShellProfiles.theta_zero t (by nlinarith only [ht]))
  have hCK : 0 ≤ K * C := mul_nonneg hK (zero_le_one.trans hC)
  have hKP : 0 ≤ K * (4 * Real.pi) := mul_nonneg hK (by positivity)
  have hC2 : 1 ≤ secondConstant C K := by dsimp [secondConstant]; nlinarith only [hC, hCK, hKP]
  have hC3 : 1 ≤ thirdConstant C K := by dsimp [thirdConstant]; nlinarith only [hC, hCK, hKP]
  refine ⟨radiusConstant C K, secondConstant C K, thirdConstant C K, radiusConstant_ge_one C K hC hK, hC2, hC3, ?_⟩
  intro F inst inst' inst'' n V hV R f
  have hSmooth : ContDiff ℝ ∞ f := actual_localized_chain_smooth _ FangqingPublicShellProfiles.theta_smooth R n V
  have hJets : ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ secondConstant C K ∧
      ‖iteratedFDeriv ℝ 3 f x‖ ≤ thirdConstant C K := by
    intro x
    exact actual_localized_high_jets_from_bounds _ (FangqingPublicShellProfiles.theta_smooth.of_le (by decide))
      FangqingPublicShellProfiles.theta_range C K hC hK n V x (hChain F n V hV x)
      (fun j hj hj3 => hGate F (chainRadius n C K) (chainRadius_positive n C K hC hK) (0 : F) x j hj hj3)
  have hHess := hessian_lipschitz_from_third_jet f (hSmooth.of_le (by decide))
    (⟨thirdConstant C K, zero_le_one.trans hC3⟩ : ℝ≥0) (fun x => (hJets x).2)
  refine ⟨hSmooth, ?_, fun x y => hHess.norm_sub_le x y, ?_⟩
  · intro x
    rw [hessian_norm_eq_second_jet]
    exact (hJets x).1
  · intro x hx
    exact actual_localized_exterior_lower_from_bounds _ (FangqingPublicShellProfiles.theta_smooth.of_le (by decide))
      FangqingPublicShellProfiles.theta_range C K hC hK n V x (hChain F n V hV x).1
      (by simpa only [pow_one] using hGate F (chainRadius n C K) (chainRadius_positive n C K hC hK) (0 : F) x 1 (by omega) (by omega)) hx

end
end FangqingSingleLowerLocalizedJetBounds
end

section
-- Source component: SingleLowerActualOracleProgram.lean

open MeasureTheory
open scoped BigOperators ContDiff Topology

namespace FangqingSingleLowerActualOracleProgram

open FangqingSingleLowerPhysicalGradient FangqingSingleLowerAllDerivativeOracle
  FangqingSingleLowerLocalizedOracleLocality FangqingSingleLowerOneBoundaryReply
  OriginalPrefixOracleReplay

noncomputable section

variable {Seed E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev Response (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  AllDerivativeResponse E

def grantEveryResponse (_n : ℕ) : Decision Seed (Response E) E :=
  fun _ _ _ _ => true

def reply (theta : ℝ → ℝ) (R : ℝ) (n : ℕ) : Reply Seed E (Response E) E (n + 1) :=
  fun _ _ _ _ V x => allDerivativeOracle (localizedChain theta R n V) x

theorem virtual_disclosure_count_le_time (theta : ℝ → ℝ) (R : ℝ) (n : ℕ)
    (q : Query Seed (Response E) E) (t : ℕ) (seed : Seed) (V : Fin (n + 1) → E) :
    (virtualRun q (grantEveryResponse n) (reply theta R n) t seed V).1 ≤ t := by
  have hh := run_count_growth q (grantEveryResponse n) (maskedReply (reply theta R n)) 0 t seed V
  simpa only [zero_add, run, virtualRun] using hh

theorem actual_full_oracle_replay_from_bounded_projection (theta : ℝ → ℝ)
    (htheta : ∀ t, 49 / 16 ≤ t → theta t = 0) (R : ℝ) (hR : 0 < R)
    (n N : ℕ) (hN : N ≤ n)
    (q : Query Seed (Response E) E) (seed : Seed) (V : Fin (n + 1) → E)
    (hgood : ∀ t < N, ∀ i : Fin (n + 1),
      (virtualRun q (grantEveryResponse n) (reply theta R n) t seed V).1 ≤ i.val →
      |inner ℝ (V i) (clippedCandidate R
        (q t seed (virtualRun q (grantEveryResponse n) (reply theta R n) t seed V)))| ≤ 1 / 4) :
    (∀ t ≤ N, run q (grantEveryResponse n) (reply theta R n) t seed V =
      virtualRun q (grantEveryResponse n) (reply theta R n) t seed V) ∧
    (∀ t < N, q t seed (run q (grantEveryResponse n) (reply theta R n) t seed V) =
      q t seed (virtualRun q (grantEveryResponse n) (reply theta R n) t seed V)) := by
  apply real_virtual_execution_replay
  intro t ht
  let st := virtualRun q (grantEveryResponse n) (reply theta R n) t seed V
  have hk : st.1 < n + 1 := by
    have htime := virtual_disclosure_count_le_time theta R n q t seed V
    change st.1 ≤ t at htime
    omega
  have ha : advance (n + 1) st.1
      (grantEveryResponse n t seed st (q t seed st)) = st.1 + 1 := by
    simp only [grantEveryResponse, advance, hk, and_self, if_true]
  change allDerivativeOracle (localizedChain theta R n V) (q t seed st) =
    allDerivativeOracle (localizedChain theta R n
      (FangqingPrefixAdaptedModel.mask _ V)) (q t seed st)
  rw [ha]
  exact actual_entire_reply_equals_one_boundary_prefix theta htheta R hR n st.1 V
    (q t seed st) (hgood t ht)

theorem actual_unqueried_output_replay (theta : ℝ → ℝ)
    (htheta : ∀ t, 49 / 16 ≤ t → theta t = 0) (R : ℝ) (hR : 0 < R)
    (n N : ℕ) (hN : N ≤ n)
    (q : Query Seed (Response E) E) (out : Seed → State (Response E) → E)
    (seed : Seed) (V : Fin (n + 1) → E)
    (hgood : ∀ t < N, ∀ i : Fin (n + 1),
      (virtualRun q (grantEveryResponse n) (reply theta R n) t seed V).1 ≤ i.val →
      |inner ℝ (V i) (clippedCandidate R
        (q t seed (virtualRun q (grantEveryResponse n) (reply theta R n) t seed V)))| ≤ 1 / 4) :
    out seed (run q (grantEveryResponse n) (reply theta R n) N seed V) =
      out seed (virtualRun q (grantEveryResponse n) (reply theta R n) N seed V) :=
  congrArg (out seed) ((actual_full_oracle_replay_from_bounded_projection theta htheta R hR
    n N hN q seed V hgood).1 N le_rfl)

section Measurability

variable [MeasurableSpace Seed] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace (Response E)] [BorelSpace (Response E)]

theorem actual_infinite_reply_measurable (theta : ℝ → ℝ)
    (htheta : ContDiff ℝ ∞ theta) (R : ℝ) (n t : ℕ) :
    Measurable (fun x : Seed × State (Response E) × ℕ × (Fin (n + 1) → E) × E =>
      reply theta R n t x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) := by
  exact (actual_complete_infinite_oracle_jointly_continuous theta htheta R n).measurable.comp
    ((measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))).prodMk
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))))

end Measurability
end
end FangqingSingleLowerActualOracleProgram
end

section
-- Source component: SingleLowerActualHaarLowerKernel.lean

open MeasureTheory ProbabilityTheory
open scoped BigOperators ContDiff Topology

namespace FangqingSingleLowerActualHaarLowerKernel

open FangqingSingleLowerPhysicalGradient FangqingSingleLowerLocalizedGap
  FangqingSingleLowerAllDerivativeOracle FangqingSingleLowerLocalizedOracleLocality
  FangqingSingleLowerActualOracleProgram OriginalPrefixOracleReplay
  OriginalPrefixOracleHaarBridge

noncomputable section

variable {Ω Seed E : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace Seed] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  [MeasurableSpace (Response E)] [BorelSpace (Response E)]

def badSet (theta : ℝ → ℝ) (R : ℝ) (n N : ℕ)
    (q : Query Seed (Response E) E) (out : Seed → State (Response E) → E)
    (X : Ω → Seed) (V : Ω → (Fin (n + 1) → E)) : Set Ω :=
  ⋃ t : Fin (N + 1), ⋃ j : Fin 1, ⋃ i : Fin (n + 1),
    {sample | originalCount q (grantEveryResponse n) (reply theta R n) X V t.val sample ≤ i.val ∧
      (1 / 4 : ℝ) < |inner ℝ (V sample i)
        (candidates q (grantEveryResponse n) (reply theta R n) out X V N 1
          (fun _ => id) (2 * R) t j sample)|}

theorem actual_bad_set_probability (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : MeasurableSpace Ω) (hG : G ≤ mΩ) (X : Ω → Seed)
    (hX : @Measurable Ω Seed G inferInstance X) (V : Ω → (Fin (n + 1) → E))
    (hV : @Measurable Ω (Fin (n + 1) → E) mΩ inferInstance V)
    (hind : @Indep Ω G ((inferInstance : MeasurableSpace (Fin (n + 1) → E)).comap V) mΩ μ)
    (b : OrthonormalBasis (Fin d) ℝ E) (hmd : n + 1 ≤ d)
    (hlaw : @Measure.map Ω (Fin (n + 1) → E) mΩ inferInstance V μ =
      FangqingAdaptiveHaarOriginal.frameLaw b hmd)
    (theta : ℝ → ℝ) (htheta : ContDiff ℝ ∞ theta) (R : ℝ) (hR : 0 < R)
    (N : ℕ) (q : Query Seed (Response E) E)
    (hq : ∀ t, Measurable (fun x : Seed × State (Response E) => q t x.1 x.2))
    (out : Seed → State (Response E) → E)
    (hout : Measurable (fun x : Seed × State (Response E) => out x.1 x.2))
    (zeta : ℝ) (hzeta : 0 < zeta)
    (hbudget : 2 * (2 * R) ^ 2 / (1 / 4 : ℝ) ^ 2 *
      Real.log ((2 * 1 * (N + 1) * (n + 1)) / zeta) ≤ ((d - (n + 1) : ℕ) : ℝ)) :
    μ.real (badSet theta R n N q out X V) ≤ zeta := by
  have hh := generated_candidates_and_disclosure_haar_bound (mΩ := mΩ) μ G hG X hX V hV hind b hmd hlaw
    q (grantEveryResponse n) (reply theta R n) hq (fun _ => measurable_const)
    (actual_infinite_reply_measurable theta htheta R n) out hout N 1 (fun _ => id)
    (fun _ => measurable_id) (2 * R) (1 / 4) (by positivity) (by norm_num)
  apply hh.2 zeta hzeta (by omega) (by omega) (by norm_num)
  simpa only [Nat.cast_add, Nat.cast_one] using hbudget

theorem not_bad_controls_every_actual_query (theta : ℝ → ℝ) (R : ℝ) (n N : ℕ)
    (q : Query Seed (Response E) E) (out : Seed → State (Response E) → E)
    (X : Ω → Seed) (V : Ω → (Fin (n + 1) → E)) (sample : Ω)
    (hgood : sample ∉ badSet theta R n N q out X V) :
    ∀ t < N, ∀ i : Fin (n + 1),
      (virtualRun q (grantEveryResponse n) (reply theta R n) t (X sample) (V sample)).1 ≤ i.val →
      |inner ℝ (V sample i) (clippedCandidate R
        (q t (X sample) (virtualRun q (grantEveryResponse n) (reply theta R n) t (X sample) (V sample))))| ≤ 1 / 4 := by
  intro t ht i hi
  by_contra h
  apply hgood
  apply Set.mem_iUnion.mpr
  refine ⟨⟨t, by omega⟩, ?_⟩
  apply Set.mem_iUnion.mpr
  refine ⟨0, ?_⟩
  apply Set.mem_iUnion.mpr
  refine ⟨i, hi, ?_⟩
  simpa only [candidates, queryOrTerminal, ht, if_true, id_eq, zeroClip, clippedCandidate]
    using lt_of_not_ge h

theorem not_bad_controls_actual_terminal_output (theta : ℝ → ℝ) (R : ℝ) (n N : ℕ)
    (q : Query Seed (Response E) E) (out : Seed → State (Response E) → E)
    (X : Ω → Seed) (V : Ω → (Fin (n + 1) → E)) (sample : Ω)
    (hgood : sample ∉ badSet theta R n N q out X V) :
    ∀ i : Fin (n + 1),
      (virtualRun q (grantEveryResponse n) (reply theta R n) N (X sample) (V sample)).1 ≤ i.val →
      |inner ℝ (V sample i) (clippedCandidate R
        (out (X sample) (virtualRun q (grantEveryResponse n) (reply theta R n) N (X sample) (V sample))))| ≤ 1 / 4 := by
  intro i hi
  by_contra h
  apply hgood
  apply Set.mem_iUnion.mpr
  refine ⟨Fin.last N, ?_⟩
  apply Set.mem_iUnion.mpr
  refine ⟨0, ?_⟩
  apply Set.mem_iUnion.mpr
  refine ⟨i, hi, ?_⟩
  simpa only [candidates, queryOrTerminal, Fin.val_last, lt_self_iff_false,
    if_false, id_eq, zeroClip, clippedCandidate] using lt_of_not_ge h

theorem actual_output_has_large_gradient_on_good_event (theta : ℝ → ℝ)
    (hone : ∀ t, t ≤ 9 / 4 → theta t = 1)
    (hzero : ∀ t, 49 / 16 ≤ t → theta t = 0) (R : ℝ) (hR : 0 < R)
    (n N : ℕ) (hN : N ≤ n)
    (q : Query Seed (Response E) E) (out : Seed → State (Response E) → E)
    (X : Ω → Seed) (V : Ω → (Fin (n + 1) → E)) (sample : Ω) (hV : Orthonormal ℝ (V sample))
    (hexterior : ∀ z : E, (3 / 2 : ℝ) * R ≤ ‖z‖ →
      (9 / 10 : ℝ) ≤ ‖fderiv ℝ (localizedChain theta R n (V sample)) z‖)
    (hgood : sample ∉ badSet theta R n N q out X V) :
    (9 / 10 : ℝ) ≤ ‖fderiv ℝ (localizedChain theta R n (V sample))
      (out (X sample) (run q (grantEveryResponse n) (reply theta R n) N (X sample) (V sample)))‖ := by
  have hqgood := not_bad_controls_every_actual_query theta R n N q out X V sample hgood
  have hreplay := actual_unqueried_output_replay theta hzero R hR n N hN q out (X sample) (V sample) hqgood
  rw [hreplay]
  let z := out (X sample) (virtualRun q (grantEveryResponse n) (reply theta R n) N (X sample) (V sample))
  change (9 / 10 : ℝ) ≤ ‖fderiv ℝ (localizedChain theta R n (V sample)) z‖
  by_cases hz : ‖z‖ < (3 / 2 : ℝ) * R
  · apply actual_localized_inside_gradient_lower theta hone R hR n (V sample) hV z hz
    have htime := virtual_disclosure_count_le_time theta R n q N (X sample) (V sample)
    have hlast := not_bad_controls_actual_terminal_output theta R n N q out X V sample hgood
      (Fin.last n) (by simp only [Fin.val_last]; omega)
    have hclip : clippedCandidate R z = z := by
      unfold clippedCandidate
      rw [if_pos (by linarith only [hz, hR] : ‖z‖ ≤ 2 * R)]
    change |inner ℝ (V sample (Fin.last n)) (clippedCandidate R z)| ≤ 1 / 4 at hlast
    rw [hclip] at hlast
    exact ⟨Fin.last n, by linarith only [hlast]⟩
  · exact hexterior z (le_of_not_gt hz)

end
end FangqingSingleLowerActualHaarLowerKernel
end

section
-- Source component: SingleLowerFixedHaarWorld.lean

open MeasureTheory ProbabilityTheory
open scoped BigOperators ContDiff Topology ENNReal

namespace FangqingSingleLowerFixedHaarWorld

open FangqingSingleLowerPhysicalGradient FangqingSingleLowerAllDerivativeOracle
  FangqingSingleLowerActualOracleProgram FangqingSingleLowerActualHaarLowerKernel
  OriginalPrefixOracleReplay FangqingAdaptiveHaarProduct FangqingAdaptiveHaarConcrete

noncomputable section

variable {Seed E : Type*} [MeasurableSpace Seed]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  [MeasurableSpace (Response E)] [BorelSpace (Response E)]

abbrev Group (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :=
  FangqingOrthogonalHaar.Group E

def outputAt (theta : ℝ → ℝ) (R : ℝ) (n N : ℕ)
    (b : OrthonormalBasis (Fin d) ℝ E) (hmd : n + 1 ≤ d)
    (q : Query Seed (Response E) E) (out : Seed → State (Response E) → E)
    (g : Group E) (seed : Seed) : E :=
  out seed (run q (grantEveryResponse n) (reply theta R n) N seed (frame (basisPrefix b hmd) g))

def failureSet (theta : ℝ → ℝ) (R : ℝ) (n N : ℕ)
    (b : OrthonormalBasis (Fin d) ℝ E) (hmd : n + 1 ≤ d)
    (q : Query Seed (Response E) E) (out : Seed → State (Response E) → E) : Set (Group E × Seed) :=
  {p | (9 / 10 : ℝ) ≤ ‖fderiv ℝ (localizedChain theta R n (frame (basisPrefix b hmd) p.1))
    (outputAt theta R n N b hmd q out p.1 p.2)‖}

theorem actual_fixed_world_failure_event_measurable (theta : ℝ → ℝ)
    (htheta : ContDiff ℝ ∞ theta) (R : ℝ) (n N : ℕ)
    (b : OrthonormalBasis (Fin d) ℝ E) (hmd : n + 1 ≤ d)
    (q : Query Seed (Response E) E)
    (hq : ∀ t, Measurable (fun x : Seed × State (Response E) => q t x.1 x.2))
    (out : Seed → State (Response E) → E)
    (hout : Measurable (fun x : Seed × State (Response E) => out x.1 x.2)) :
    MeasurableSet (failureSet theta R n N b hmd q out) := by
  have hframe : Measurable (frame (basisPrefix b hmd)) := measurable_frame _
  have hpull : Measurable (fun p : Group E × Seed => (p.2, frame (basisPrefix b hmd) p.1)) :=
    measurable_snd.prodMk (hframe.comp measurable_fst)
  have hrun := run_measurable q (grantEveryResponse n) (reply theta R n) hq
    (fun _ => measurable_const) (actual_infinite_reply_measurable theta htheta R n) N
  have houtcome : Measurable (fun p : Group E × Seed => outputAt theta R n N b hmd q out p.1 p.2) :=
    hout.comp (measurable_snd.prodMk (hrun.comp hpull))
  have hc : Continuous (fun p : (Fin (n + 1) → E) × E =>
      ‖iteratedFDeriv ℝ 1 (localizedChain theta R n p.1) p.2‖) :=
    (every_partial_jet_is_jointly_smooth (localizedChain theta R n)
      (actual_localized_family_jointly_smooth theta htheta R n) 1).continuous.norm
  have hs : Measurable (fun p : Group E × Seed =>
      ‖fderiv ℝ (localizedChain theta R n (frame (basisPrefix b hmd) p.1))
        (outputAt theta R n N b hmd q out p.1 p.2)‖) := by
    simpa only [norm_iteratedFDeriv_one, Function.comp_def] using
      hc.measurable.comp ((hframe.comp measurable_fst).prodMk houtcome)
  exact measurableSet_le measurable_const hs

theorem exists_fixed_seed_independent_hard_world (seeds : Measure Seed)
    [IsProbabilityMeasure seeds] (theta : ℝ → ℝ) (htheta : ContDiff ℝ ∞ theta)
    (hone : ∀ t, t ≤ 9 / 4 → theta t = 1)
    (hzero : ∀ t, 49 / 16 ≤ t → theta t = 0) (R : ℝ) (hR : 0 < R)
    (n N : ℕ) (hN : N ≤ n) (b : OrthonormalBasis (Fin d) ℝ E) (hmd : n + 1 ≤ d)
    (q : Query Seed (Response E) E)
    (hq : ∀ t, Measurable (fun x : Seed × State (Response E) => q t x.1 x.2))
    (out : Seed → State (Response E) → E)
    (hout : Measurable (fun x : Seed × State (Response E) => out x.1 x.2))
    (hexterior : ∀ (g : Group E) (z : E), (3 / 2 : ℝ) * R ≤ ‖z‖ →
      (9 / 10 : ℝ) ≤ ‖fderiv ℝ (localizedChain theta R n (frame (basisPrefix b hmd) g)) z‖)
    (hbudget : 2 * (2 * R) ^ 2 / (1 / 4 : ℝ) ^ 2 *
      Real.log ((2 * 1 * (N + 1) * (n + 1)) / (1 / 6 : ℝ)) ≤ ((d - (n + 1) : ℕ) : ℝ)) :
    ∃ g : Group E, (2 / 3 : ℝ≥0∞) ≤ seeds
      {seed | (9 / 10 : ℝ) ≤
        ‖fderiv ℝ (localizedChain theta R n (frame (basisPrefix b hmd) g))
          (outputAt theta R n N b hmd q out g seed)‖} := by
  let frames := FangqingOrthogonalHaar.rightHaar E
  let mu := frames.prod seeds
  let Vf : Group E × Seed → (Fin (n + 1) → E) := fun p => frame (basisPrefix b hmd) p.1
  have hframe : Measurable (frame (basisPrefix b hmd)) := measurable_frame _
  have hVf : Measurable Vf := hframe.comp measurable_fst
  have hlaw : mu.map Vf = FangqingAdaptiveHaarOriginal.frameLaw b hmd := by
    change (frames.prod seeds).map (frame (basisPrefix b hmd) ∘ Prod.fst) = frames.map _
    rw [← Measure.map_map hframe measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]
  have hind : IndepFun (Prod.snd : Group E × Seed → Seed) Vf mu :=
    (indepFun_prod (μ := frames) (ν := seeds) hframe measurable_id).symm
  have hbad : mu.real (badSet theta R n N q out Prod.snd Vf) ≤ (1 / 6 : ℝ) := by
    let actualSpace : MeasurableSpace (Group E × Seed) := inferInstance
    let G : MeasurableSpace (Group E × Seed) := MeasurableSpace.comap Prod.snd inferInstance
    have hG : G ≤ actualSpace :=
      (measurable_snd : @Measurable (Group E × Seed) Seed actualSpace inferInstance Prod.snd).comap_le
    exact actual_bad_set_probability (mΩ := actualSpace) mu G hG Prod.snd (comap_measurable Prod.snd)
      Vf hVf hind b hmd hlaw theta htheta R hR N q hq out hout (1 / 6) (by norm_num) hbudget
  have hf : MeasurableSet (failureSet theta R n N b hmd q out) :=
    actual_fixed_world_failure_event_measurable theta htheta R n N b hmd q hq out hout
  have hsubset : (failureSet theta R n N b hmd q out)ᶜ ⊆
      badSet theta R n N q out Prod.snd Vf := by
    intro p hp
    by_contra hgood
    apply hp
    exact actual_output_has_large_gradient_on_good_event theta hone hzero R hR n N hN q out
      Prod.snd Vf p (FangqingAdaptiveHaarOriginal.frame_orthonormal b hmd p.1)
      (hexterior p.1) hgood
  have hcomp : mu.real (failureSet theta R n N b hmd q out)ᶜ ≤ (1 / 6 : ℝ) :=
    (measureReal_mono hsubset).trans hbad
  have htotal := measureReal_add_measureReal_compl (μ := mu) hf
  rw [probReal_univ] at htotal
  have havereal : (2 / 3 : ℝ) ≤ mu.real (failureSet theta R n N b hmd q out) := by
    linarith only [hcomp, htotal]
  have haveave : (2 / 3 : ℝ≥0∞) ≤ mu (failureSet theta R n N b hmd q out) := by
    have hh := ENNReal.ofReal_le_ofReal havereal
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top mu _)] at hh
    have he : ENNReal.ofReal (2 / 3 : ℝ) = (2 / 3 : ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]
      norm_num
    rw [he] at hh
    exact hh
  exact OriginalSerialProductProbability.exists_fixed_frame_failure frames seeds
    (failureSet theta R n N b hmd q out) hf (2 / 3) haveave

end
end FangqingSingleLowerFixedHaarWorld
end

section
-- Source component: SingleLowerNormalizedLower.lean

open MeasureTheory
open scoped ContDiff ENNReal

namespace FangqingSingleLowerNormalizedLower

open FangqingSingleLowerPhysicalGradient FangqingSingleLowerAllDerivativeOracle
  FangqingSingleLowerActualOracleProgram FangqingSingleLowerFixedHaarWorld
  FangqingSingleLowerLocalizedJetBounds FangqingSingleLowerLocalizedGap
  OriginalPrefixOracleReplay FangqingAdaptiveHaarProduct FangqingAdaptiveHaarConcrete

noncomputable section

universe u v

theorem actual_universal_normalized_all_derivative_lower_family :
    ∃ CR C2 C3 : ℝ, 1 ≤ CR ∧ 1 ≤ C2 ∧ 1 ≤ C3 ∧
      ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
        [MeasurableSpace (Response E)] [BorelSpace (Response E)],
      ∀ (Seed : Type v) [MeasurableSpace Seed] (seeds : Measure Seed) [IsProbabilityMeasure seeds],
      ∀ (n N d : ℕ), N ≤ n → ∀ (b : OrthonormalBasis (Fin d) ℝ E) (hmd : n + 1 ≤ d),
      ∀ (q : Query Seed (Response E) E),
        (∀ t, Measurable (fun x : Seed × State (Response E) => q t x.1 x.2)) →
      ∀ (out : Seed → State (Response E) → E),
        Measurable (fun x : Seed × State (Response E) => out x.1 x.2) →
      let R := CR * Real.sqrt ((n + 1 : ℕ) : ℝ)
      2 * (2 * R) ^ 2 / (1 / 4 : ℝ) ^ 2 *
        Real.log ((2 * 1 * (N + 1) * (n + 1)) / (1 / 6 : ℝ)) ≤ ((d - (n + 1) : ℕ) : ℝ) →
      ∃ g : FangqingSingleLowerFixedHaarWorld.Group E,
        let f := localizedChain FangqingPublicShellProfiles.theta R n (frame (basisPrefix b hmd) g)
        ContDiff ℝ ∞ f ∧ f 0 - sInf (Set.range f) ≤ 4 * Real.pi * (n + 1) ∧
          (∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C2) ∧
          (∀ x y, ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤ C3 * ‖x - y‖) ∧
          (2 / 3 : ℝ≥0∞) ≤ seeds {seed | (9 / 10 : ℝ) ≤
            ‖fderiv ℝ f (outputAt FangqingPublicShellProfiles.theta R n N b hmd q out g seed)‖} := by
  obtain ⟨CR, C2, C3, hCR, hC2, hC3, hclass⟩ := universal_actual_localized_chain_class.{u}
  refine ⟨CR, C2, C3, hCR, hC2, hC3, ?_⟩
  intro E inst inst' inst'' inst''' instM instB instN instR instBR
    Seed instSeed seeds instProb n N d hN b hmd q hq out hout R hbudget
  have hRp : 0 < R := by dsimp [R]; positivity
  have hone : ∀ t : ℝ, t ≤ 9 / 4 → FangqingPublicShellProfiles.theta t = 1 :=
    FangqingPublicShellProfiles.theta_one
  have hzero : ∀ t : ℝ, 49 / 16 ≤ t → FangqingPublicShellProfiles.theta t = 0 :=
    FangqingPublicShellProfiles.theta_zero
  obtain ⟨g, hg⟩ := exists_fixed_seed_independent_hard_world seeds FangqingPublicShellProfiles.theta
    FangqingPublicShellProfiles.theta_smooth hone hzero R hRp n N hN b hmd q hq out hout
    (fun g z hz => (by norm_num : (9 / 10 : ℝ) ≤ 1).trans
      ((hclass E n (frame (basisPrefix b hmd) g)
        (FangqingAdaptiveHaarOriginal.frame_orthonormal b hmd g)).2.2.2 z hz)) hbudget
  have hfg := hclass E n (frame (basisPrefix b hmd) g)
    (FangqingAdaptiveHaarOriginal.frame_orthonormal b hmd g)
  refine ⟨g, hfg.1, ?_, hfg.2.1, hfg.2.2.1, hg⟩
  exact actual_localized_chain_initial_gap FangqingPublicShellProfiles.theta
    FangqingPublicShellProfiles.theta_range (hone 0 (by norm_num)) R n (frame (basisPrefix b hmd) g)

end
end FangqingSingleLowerNormalizedLower
end

section
-- Source component: SingleLowerOracleRescaling.lean

open scoped BigOperators ContDiff Topology NNReal

namespace FangqingSingleLowerOracleRescaling

open MeasureTheory FangqingSingleLowerAllDerivativeOracle
  FangqingSingleLowerActualOracleProgram OriginalPrefixOracleReplay

noncomputable section
set_option maxHeartbeats 4500000

variable {Seed E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def scaledFunction (alpha beta : ℝ) (f : E → ℝ) (x : E) : ℝ := alpha * f (beta⁻¹ • x)

def scaleJet (alpha beta : ℝ) (r : AllDerivativeResponse E) : AllDerivativeResponse E :=
  fun j => (alpha * beta⁻¹ ^ j) • r j

def scaleState (alpha beta : ℝ) (st : State (AllDerivativeResponse E)) : State (AllDerivativeResponse E) :=
  (st.1, fun t => scaleJet alpha beta (st.2 t))

def baseQuery (alpha beta : ℝ) (q : Query Seed (AllDerivativeResponse E) E) :
    Query Seed (AllDerivativeResponse E) E :=
  fun t seed st => beta⁻¹ • q t seed (scaleState alpha beta st)

def baseOutput (alpha beta : ℝ) (out : Seed → State (AllDerivativeResponse E) → E) :
    Seed → State (AllDerivativeResponse E) → E :=
  fun seed st => beta⁻¹ • out seed (scaleState alpha beta st)

def familyReply {m : ℕ} (f : (Fin m → E) → E → ℝ) :
    Reply Seed E (AllDerivativeResponse E) E m :=
  fun _ _ _ _ V x => allDerivativeOracle (f V) x

def scaledFamily {m : ℕ} (alpha beta : ℝ) (f : (Fin m → E) → E → ℝ) :
    (Fin m → E) → E → ℝ := fun V => scaledFunction alpha beta (f V)

theorem scaledFunction_smooth (alpha beta : ℝ) (f : E → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (scaledFunction alpha beta f) :=
  contDiff_const.mul (hf.comp (contDiff_const.smul contDiff_id))

theorem actual_all_order_oracle_scaling (alpha beta : ℝ) (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (x : E) :
    allDerivativeOracle (scaledFunction alpha beta f) x =
      scaleJet alpha beta (allDerivativeOracle f (beta⁻¹ • x)) := by
  funext j
  change iteratedFDeriv ℝ j (fun y : E => alpha • f (beta⁻¹ • y)) x =
    (alpha * beta⁻¹ ^ j) • iteratedFDeriv ℝ j f (beta⁻¹ • x)
  have hj : ContDiff ℝ j f := hf.of_le (mod_cast le_top)
  have hc : ContDiffAt ℝ j (fun y : E => f (beta⁻¹ • y)) x :=
    (hj.comp (contDiff_const.smul contDiff_id)).contDiffAt
  rw [iteratedFDeriv_const_smul_apply' hc, congrFun (iteratedFDeriv_comp_const_smul beta⁻¹ hj) x, smul_smul]

theorem scaleJet_zero (alpha beta : ℝ) : scaleJet alpha beta (0 : AllDerivativeResponse E) = 0 := by
  funext j
  simp only [scaleJet, Pi.zero_apply, smul_zero]

theorem scaleState_zero (alpha beta : ℝ) : scaleState alpha beta (0 : State (AllDerivativeResponse E)) = 0 := by
  apply Prod.ext
  · rfl
  · funext t
    exact scaleJet_zero alpha beta

/-- Exact genuine oracle-program conjugacy: the original program sees the
    all-order jets of one scaled fixed family and uses the same seed. -/
theorem actual_scaled_program_conjugacy
    (alpha beta : ℝ) (n : ℕ) (f : (Fin (n + 1) → E) → E → ℝ)
    (hf : ∀ V, ContDiff ℝ ∞ (f V)) (q : Query Seed (AllDerivativeResponse E) E)
    (N : ℕ) (seed : Seed) (V : Fin (n + 1) → E) :
    run q (grantEveryResponse n) (familyReply (scaledFamily alpha beta f)) N seed V =
      scaleState alpha beta (run (baseQuery alpha beta q) (grantEveryResponse n) (familyReply f) N seed V) := by
  induction N with
  | zero =>
      apply Prod.ext
      · rfl
      · funext t
        exact (scaleJet_zero alpha beta).symm
  | succ N ih =>
      simp only [run]
      rw [ih]
      apply Prod.ext
      · rfl
      · funext i
        by_cases hi : i = N
        · subst i
          simp only [transition, scaleState, familyReply, scaledFamily, baseQuery, Function.update_self]
          exact actual_all_order_oracle_scaling alpha beta (f V) (hf V) _
        · simp only [transition, scaleState, familyReply, scaledFamily, baseQuery, Function.update_apply, hi, if_false]

theorem actual_unqueried_output_conjugacy
    (alpha beta : ℝ) (n : ℕ) (f : (Fin (n + 1) → E) → E → ℝ)
    (hf : ∀ V, ContDiff ℝ ∞ (f V)) (q : Query Seed (AllDerivativeResponse E) E)
    (out : Seed → State (AllDerivativeResponse E) → E)
    (N : ℕ) (seed : Seed) (V : Fin (n + 1) → E) :
    baseOutput alpha beta out seed (run (baseQuery alpha beta q) (grantEveryResponse n) (familyReply f) N seed V) =
      beta⁻¹ • out seed (run q (grantEveryResponse n) (familyReply (scaledFamily alpha beta f)) N seed V) := by
  rw [actual_scaled_program_conjugacy alpha beta n f hf q N seed V]
  rfl

def actualQueryTrace (n : ℕ) (f : (Fin (n + 1) → E) → E → ℝ)
    (q : Query Seed (AllDerivativeResponse E) E) : ℕ → Seed → (Fin (n + 1) → E) → List E
  | 0, _, _ => []
  | N + 1, seed, V => actualQueryTrace n f q N seed V ++
      [q N seed (run q (grantEveryResponse n) (familyReply f) N seed V)]

theorem actualQueryTrace_length (n : ℕ) (f : (Fin (n + 1) → E) → E → ℝ)
    (q : Query Seed (AllDerivativeResponse E) E) (N : ℕ) (seed : Seed) (V : Fin (n + 1) → E) :
    (actualQueryTrace n f q N seed V).length = N := by
  induction N with
  | zero => rfl
  | succ N ih => simp only [actualQueryTrace, List.length_append, List.length_singleton, ih]

theorem scaled_query_trace_same_paid_calls
    (alpha beta : ℝ) (hbeta : beta ≠ 0) (n : ℕ) (f : (Fin (n + 1) → E) → E → ℝ)
    (hf : ∀ V, ContDiff ℝ ∞ (f V)) (q : Query Seed (AllDerivativeResponse E) E)
    (N : ℕ) (seed : Seed) (V : Fin (n + 1) → E) :
    actualQueryTrace n (scaledFamily alpha beta f) q N seed V =
      (actualQueryTrace n f (baseQuery alpha beta q) N seed V).map (fun x => beta • x) := by
  induction N with
  | zero => rfl
  | succ N ih =>
      simp only [actualQueryTrace, List.map_append, List.map_singleton, ih,
        actual_scaled_program_conjugacy alpha beta n f hf q N seed V, baseQuery]
      congr 2
      simp only [smul_smul, mul_inv_cancel₀ hbeta, one_smul]

theorem scaled_gradient_norm (alpha beta : ℝ) (halpha : 0 < alpha) (hbeta : 0 < beta)
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (x : E) :
    ‖fderiv ℝ (scaledFunction alpha beta f) x‖ =
      (alpha / beta) * ‖fderiv ℝ f (beta⁻¹ • x)‖ := by
  have hh := congrArg (fun r : AllDerivativeResponse E => ‖r 1‖) (actual_all_order_oracle_scaling alpha beta f hf x)
  simpa only [allDerivativeOracle, scaleJet, pow_one, norm_smul, Real.norm_eq_abs,
    abs_of_pos (mul_pos halpha (inv_pos.mpr hbeta)), norm_iteratedFDeriv_one, div_eq_mul_inv] using hh

theorem actual_scaled_gradient_failure
    (alpha beta delta : ℝ) (halpha : 0 < alpha) (hbeta : 0 < beta) (hdelta : 0 < delta)
    (hratio : alpha / beta = 4 * delta) (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (x : E)
    (hfail : (9 / 10 : ℝ) ≤ ‖fderiv ℝ f (beta⁻¹ • x)‖) :
    delta < ‖fderiv ℝ (scaledFunction alpha beta f) x‖ := by
  rw [scaled_gradient_norm alpha beta halpha hbeta f hf x, hratio]
  have hh := mul_le_mul_of_nonneg_left hfail (by positivity : 0 ≤ 4 * delta)
  nlinarith only [hh, hdelta]

/-- Exact full Hessian identity, derived from the actual order-two oracle. -/
theorem scaled_hessian (alpha beta : ℝ) (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (x : E) :
    fderiv ℝ (fderiv ℝ (scaledFunction alpha beta f)) x =
      (alpha * beta⁻¹ ^ 2) • fderiv ℝ (fderiv ℝ f) (beta⁻¹ • x) := by
  ext v w
  have hh := congrArg (fun r : AllDerivativeResponse E => r 2 ![v, w])
    (actual_all_order_oracle_scaling alpha beta f hf x)
  simpa only [allDerivativeOracle, scaleJet, ContinuousMultilinearMap.smul_apply,
    iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    ContinuousLinearMap.smul_apply, smul_eq_mul] using hh

theorem scaled_hessian_bound (alpha beta C2 : ℝ) (halpha : 0 < alpha) (hbeta : 0 < beta)
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f)
    (hC2 : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C2) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (scaledFunction alpha beta f)) x‖ ≤ (alpha / beta ^ 2) * C2 := by
  rw [scaled_hessian alpha beta f hf x]
  calc
    _ ≤ ‖alpha * beta⁻¹ ^ 2‖ * ‖fderiv ℝ (fderiv ℝ f) (beta⁻¹ • x)‖ :=
      ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ (alpha / beta ^ 2) * C2 := by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < alpha * beta⁻¹ ^ 2)]
      simpa only [div_eq_mul_inv, inv_pow] using
        mul_le_mul_of_nonneg_left (hC2 (beta⁻¹ • x)) (by positivity : 0 ≤ alpha * beta⁻¹ ^ 2)

theorem scaled_hessian_lipschitz (alpha beta C3 : ℝ) (halpha : 0 < alpha) (hbeta : 0 < beta)
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f)
    (hC3 : ∀ x y, ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤ C3 * ‖x - y‖)
    (x y : E) :
    ‖fderiv ℝ (fderiv ℝ (scaledFunction alpha beta f)) x -
        fderiv ℝ (fderiv ℝ (scaledFunction alpha beta f)) y‖ ≤
      ((alpha / beta ^ 3) * C3) * ‖x - y‖ := by
  rw [scaled_hessian alpha beta f hf x, scaled_hessian alpha beta f hf y]
  have hs : (alpha * beta⁻¹ ^ 2) • fderiv ℝ (fderiv ℝ f) (beta⁻¹ • x) -
      (alpha * beta⁻¹ ^ 2) • fderiv ℝ (fderiv ℝ f) (beta⁻¹ • y) =
      (alpha * beta⁻¹ ^ 2) • (fderiv ℝ (fderiv ℝ f) (beta⁻¹ • x) -
        fderiv ℝ (fderiv ℝ f) (beta⁻¹ • y)) := by
    ext v w
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  rw [hs]
  have hnorm := ContinuousLinearMap.opNorm_smul_le (alpha * beta⁻¹ ^ 2)
    (fderiv ℝ (fderiv ℝ f) (beta⁻¹ • x) - fderiv ℝ (fderiv ℝ f) (beta⁻¹ • y))
  rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < alpha * beta⁻¹ ^ 2)] at hnorm
  have hh := mul_le_mul_of_nonneg_left (hC3 (beta⁻¹ • x) (beta⁻¹ • y))
    (by positivity : 0 ≤ alpha * beta⁻¹ ^ 2)
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hbeta)] at hh
  apply hnorm.trans
  convert hh using 1 <;> simp only [div_eq_mul_inv, inv_pow] <;> ring

theorem scaled_infimum (alpha beta : ℝ) (halpha : 0 ≤ alpha) (hbeta : beta ≠ 0) (f : E → ℝ) :
    sInf (Set.range (scaledFunction alpha beta f)) = alpha * sInf (Set.range f) := by
  have hr : Set.range (fun x : E => f (beta⁻¹ • x)) = Set.range f := by
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨beta⁻¹ • x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨beta • x, by simp only [smul_smul, inv_mul_cancel₀ hbeta, one_smul]⟩
  have hh := (Real.smul_iInf_of_nonneg halpha (fun x : E => f (beta⁻¹ • x))).symm
  change sInf (Set.range (fun x : E => alpha * f (beta⁻¹ • x))) = alpha * sInf (Set.range f)
  simpa only [smul_eq_mul, iInf, hr] using hh

theorem scaled_initial_gap (alpha beta : ℝ) (halpha : 0 ≤ alpha) (hbeta : beta ≠ 0) (f : E → ℝ) :
    scaledFunction alpha beta f 0 - sInf (Set.range (scaledFunction alpha beta f)) =
      alpha * (f 0 - sInf (Set.range f)) := by
  rw [scaled_infimum alpha beta halpha hbeta f]
  simp only [scaledFunction, smul_zero]
  ring

theorem scaled_initial_gap_bound (alpha beta B : ℝ) (halpha : 0 ≤ alpha) (hbeta : beta ≠ 0)
    (f : E → ℝ) (hgap : f 0 - sInf (Set.range f) ≤ B) :
    scaledFunction alpha beta f 0 - sInf (Set.range (scaledFunction alpha beta f)) ≤ alpha * B := by
  rw [scaled_initial_gap alpha beta halpha hbeta f]
  exact mul_le_mul_of_nonneg_left hgap halpha


theorem scaled_derivative_lipschitz (alpha beta : ℝ) (halpha : 0 < alpha) (hbeta : 0 < beta)
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (L : ℝ≥0)
    (hC2 : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ (beta ^ 2 / alpha) * L) :
    LipschitzWith L (fderiv ℝ (scaledFunction alpha beta f)) := by
  have hfs := scaledFunction_smooth alpha beta f hf
  have h2 : ContDiff ℝ 2 (scaledFunction alpha beta f) := hfs.of_le (by decide)
  apply lipschitzWith_of_nnnorm_fderiv_le
    ((h2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num))
  intro x
  have hh := scaled_hessian_bound alpha beta ((beta ^ 2 / alpha) * L) halpha hbeta f hf hC2 x
  have hc : (alpha / beta ^ 2) * ((beta ^ 2 / alpha) * (L : ℝ)) = L := by
    field_simp [halpha.ne', hbeta.ne']
  rw [hc] at hh
  exact_mod_cast hh

/-- The external smooth class and actual initial gap follow from base-class
    bounds and the explicit three scalar normalization inequalities. -/
theorem scaled_actual_class_and_initial_gap
    (alpha beta C2 C3 B ell rho Delta : ℝ) (halpha : 0 < alpha) (hbeta : 0 < beta)
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f)
    (hC2 : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C2)
    (hC3 : ∀ x y, ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤ C3 * ‖x - y‖)
    (hgap : f 0 - sInf (Set.range f) ≤ B)
    (hL : (alpha / beta ^ 2) * C2 ≤ ell) (hrho : (alpha / beta ^ 3) * C3 ≤ rho)
    (hDelta : alpha * B ≤ Delta) :
    ContDiff ℝ ∞ (scaledFunction alpha beta f) ∧
      scaledFunction alpha beta f 0 - sInf (Set.range (scaledFunction alpha beta f)) ≤ Delta ∧
      (∀ x, ‖fderiv ℝ (fderiv ℝ (scaledFunction alpha beta f)) x‖ ≤ ell) ∧
      (∀ x y, ‖fderiv ℝ (fderiv ℝ (scaledFunction alpha beta f)) x -
        fderiv ℝ (fderiv ℝ (scaledFunction alpha beta f)) y‖ ≤ rho * ‖x - y‖) := by
  refine ⟨scaledFunction_smooth alpha beta f hf,
    (scaled_initial_gap_bound alpha beta B halpha.le hbeta.ne' f hgap).trans hDelta,
    fun x => (scaled_hessian_bound alpha beta C2 halpha hbeta f hf hC2 x).trans hL, ?_⟩
  intro x y
  exact (scaled_hessian_lipschitz alpha beta C3 halpha hbeta f hf hC3 x y).trans
    (mul_le_mul_of_nonneg_right hrho (norm_nonneg _))


section Measurability
variable [MeasurableSpace Seed] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (AllDerivativeResponse E)] [BorelSpace (AllDerivativeResponse E)]

theorem scaleJet_continuous (alpha beta : ℝ) : Continuous (scaleJet alpha beta : AllDerivativeResponse E → AllDerivativeResponse E) :=
  continuous_pi (fun j => ((continuous_apply j).const_smul (alpha * beta⁻¹ ^ j) :
    Continuous (fun r : AllDerivativeResponse E => (alpha * beta⁻¹ ^ j) • r j)))

theorem scaleState_measurable (alpha beta : ℝ) : Measurable (scaleState alpha beta : State (AllDerivativeResponse E) → State (AllDerivativeResponse E)) := by
  apply measurable_fst.prodMk
  apply measurable_pi_lambda
  intro t
  exact (scaleJet_continuous alpha beta).measurable.comp ((measurable_pi_apply t).comp measurable_snd)

theorem baseQuery_measurable (alpha beta : ℝ) (q : Query Seed (AllDerivativeResponse E) E)
    (hq : ∀ t, Measurable (fun x : Seed × State (AllDerivativeResponse E) => q t x.1 x.2)) (t : ℕ) :
    Measurable (fun x : Seed × State (AllDerivativeResponse E) => baseQuery alpha beta q t x.1 x.2) :=
  ((hq t).comp (measurable_fst.prodMk ((scaleState_measurable alpha beta).comp measurable_snd))).const_smul beta⁻¹

theorem baseOutput_measurable (alpha beta : ℝ) (out : Seed → State (AllDerivativeResponse E) → E)
    (hout : Measurable (fun x : Seed × State (AllDerivativeResponse E) => out x.1 x.2)) :
    Measurable (fun x : Seed × State (AllDerivativeResponse E) => baseOutput alpha beta out x.1 x.2) :=
  (hout.comp (measurable_fst.prodMk ((scaleState_measurable alpha beta).comp measurable_snd))).const_smul beta⁻¹

/-- Probability transfer uses the actual base and scaled executions, including
    a terminal output that need never have been queried. -/
theorem actual_scaled_program_failure_measure
    (seeds : Measure Seed) (alpha beta delta : ℝ)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hdelta : 0 < delta)
    (hratio : alpha / beta = 4 * delta) (n : ℕ)
    (f : (Fin (n + 1) → E) → E → ℝ) (hf : ∀ V, ContDiff ℝ ∞ (f V))
    (q : Query Seed (AllDerivativeResponse E) E) (out : Seed → State (AllDerivativeResponse E) → E)
    (N : ℕ) (V : Fin (n + 1) → E) :
    seeds {seed | (9 / 10 : ℝ) ≤ ‖fderiv ℝ (f V)
      (baseOutput alpha beta out seed
        (run (baseQuery alpha beta q) (grantEveryResponse n) (familyReply f) N seed V))‖} ≤
    seeds {seed | delta < ‖fderiv ℝ (scaledFunction alpha beta (f V))
      (out seed (run q (grantEveryResponse n) (familyReply (scaledFamily alpha beta f)) N seed V))‖} := by
  apply measure_mono
  intro seed hfail
  apply actual_scaled_gradient_failure alpha beta delta halpha hbeta hdelta hratio (f V) (hf V)
  rw [← actual_unqueried_output_conjugacy alpha beta n f hf q out N seed V]
  exact hfail


end Measurability
end
end FangqingSingleLowerOracleRescaling
end

section
-- Source component: SingleLowerNormalizationScalars.lean

namespace FangqingSingleLowerNormalizationScalars

noncomputable section

def universalRateConstant (B C2 C3 : ℝ) : ℝ :=
  1 / (1000 * B * (C2 + C3 + 1))

def targetLength (B C2 C3 ell rho delta Delta : ℝ) : ℝ :=
  universalRateConstant B C2 C3 * Delta * min (ell / delta ^ 2) (Real.sqrt (rho / delta ^ 3))

theorem exact_original_two_smoothness_rate (ell rho delta : ℝ) (hrho : 0 ≤ rho)
    (hdelta : 0 < delta) :
    min (ell / delta ^ 2) (Real.sqrt (rho / delta ^ 3)) =
      min (ell * delta ^ (-2 : ℝ)) (Real.sqrt rho * delta ^ (-(3 / 2 : ℝ))) := by
  have hfirst : ell / delta ^ 2 = ell * delta ^ (-2 : ℝ) := by
    rw [Real.rpow_neg hdelta.le, Real.rpow_two]
    rfl
  have hsecond : Real.sqrt (rho / delta ^ 3) = Real.sqrt rho * delta ^ (-(3 / 2 : ℝ)) := by
    calc
      _ = (rho / delta ^ 3) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
      _ = rho ^ (1 / 2 : ℝ) / (delta ^ 3) ^ (1 / 2 : ℝ) :=
        Real.div_rpow hrho (pow_nonneg hdelta.le 3) _
      _ = rho ^ (1 / 2 : ℝ) / delta ^ (3 / 2 : ℝ) := by
        rw [← Real.rpow_natCast_mul hdelta.le 3]
        norm_num
      _ = _ := by rw [Real.rpow_neg hdelta.le, Real.sqrt_eq_rpow, div_eq_mul_inv]
  rw [hfirst, hsecond]

theorem rounded_chain_length (T : ℝ) (hT : 1 ≤ T) :
    0 < Nat.ceil T + 1 ∧ ((Nat.ceil T + 1 : ℕ) : ℝ) ≤ 3 * T ∧
      ∀ N : ℕ, (N : ℝ) < T → N ≤ Nat.ceil T := by
  refine ⟨by omega, ?_, ?_⟩
  · have hc := Nat.ceil_le_floor_add_one T
    have hc' : (Nat.ceil T : ℝ) ≤ (Nat.floor T : ℝ) + 1 := by exact_mod_cast hc
    have hf := Nat.floor_le (by linarith only [hT] : 0 ≤ T)
    push_cast
    linarith only [hc', hf, hT]
  · intro N hN
    have hh := Nat.le_ceil T
    exact_mod_cast (le_trans hN.le hh)

theorem universal_budget_margins (B C2 C3 : ℝ) (hB : 1 ≤ B)
    (hC2 : 0 ≤ C2) (hC3 : 0 ≤ C3) :
    0 < universalRateConstant B C2 C3 ∧
      48 * universalRateConstant B C2 C3 * B * C2 ≤ 1 ∧
      576 * universalRateConstant B C2 C3 ^ 2 * B ^ 2 * C3 ≤ 1 := by
  have hBp : 0 < B := by linarith only [hB]
  have hS : 0 < C2 + C3 + 1 := by positivity
  have he1 : 48 * universalRateConstant B C2 C3 * B * C2 =
      48 * C2 / (1000 * (C2 + C3 + 1)) := by
    unfold universalRateConstant
    field_simp
  have he2 : 576 * universalRateConstant B C2 C3 ^ 2 * B ^ 2 * C3 =
      576 * C3 / (1000000 * (C2 + C3 + 1) ^ 2) := by
    unfold universalRateConstant
    field_simp
    ring
  refine ⟨by unfold universalRateConstant; positivity, ?_, ?_⟩
  · rw [he1]
    apply (div_le_iff₀ (by positivity : 0 < 1000 * (C2 + C3 + 1))).mpr
    linarith only [hC2, hC3]
  · rw [he2]
    apply (div_le_iff₀ (by positivity : 0 < 1000000 * (C2 + C3 + 1) ^ 2)).mpr
    have hS1 : 1 ≤ C2 + C3 + 1 := by linarith only [hC2, hC3]
    have hS2 : C2 + C3 + 1 ≤ (C2 + C3 + 1) ^ 2 := by nlinarith only [hS1]
    nlinarith only [hS2, hC2, hC3]

theorem simultaneous_two_smoothness_normalization (B C2 C3 ell rho delta Delta : ℝ)
    (hB : 1 ≤ B) (hC2 : 0 ≤ C2) (hC3 : 0 ≤ C3)
    (hell : 0 < ell) (hrho : 0 < rho) (hdelta : 0 < delta) (hDelta : 0 < Delta)
    (hT : 1 ≤ targetLength B C2 C3 ell rho delta Delta) :
    let T := targetLength B C2 C3 ell rho delta Delta
    let m := Nat.ceil T + 1
    let amplitude := Delta / (B * m)
    let scale := amplitude / (4 * delta)
    0 < amplitude ∧ 0 < scale ∧
      amplitude * B * m = Delta ∧ amplitude / scale = 4 * delta ∧
      amplitude / scale ^ 2 * C2 ≤ ell ∧ amplitude / scale ^ 3 * C3 ≤ rho := by
  let c := universalRateConstant B C2 C3
  let T := targetLength B C2 C3 ell rho delta Delta
  let m : ℝ := (Nat.ceil T + 1 : ℕ)
  have hc := universal_budget_margins B C2 C3 hB hC2 hC3
  have hc0 : 0 < c := hc.1
  have hm0 : 0 < m := by dsimp [m]; positivity
  have hm : m ≤ 3 * T := (rounded_chain_length T hT).2.1
  have hBp : 0 < B := by linarith only [hB]
  have ht1 : T ≤ c * Delta * (ell / delta ^ 2) :=
    mul_le_mul_of_nonneg_left (min_le_left _ _) (mul_nonneg hc0.le hDelta.le)
  have ht2 : T ≤ c * Delta * Real.sqrt (rho / delta ^ 3) :=
    mul_le_mul_of_nonneg_left (min_le_right _ _) (mul_nonneg hc0.le hDelta.le)
  have hm1 : m * delta ^ 2 ≤ 3 * c * Delta * ell := by
    calc
      _ ≤ (3 * (c * Delta * (ell / delta ^ 2))) * delta ^ 2 :=
        mul_le_mul_of_nonneg_right (hm.trans (by linarith only [ht1])) (sq_nonneg delta)
      _ = _ := by field_simp
  have hm2 : m ^ 2 * delta ^ 3 ≤ 9 * c ^ 2 * Delta ^ 2 * rho := by
    have hh : m ≤ 3 * c * Delta * Real.sqrt (rho / delta ^ 3) := by
      linarith only [hm, ht2]
    have hs := pow_le_pow_left₀ hm0.le hh 2
    have hroot := Real.sq_sqrt (by positivity : 0 ≤ rho / delta ^ 3)
    calc
      _ ≤ (3 * c * Delta * Real.sqrt (rho / delta ^ 3)) ^ 2 * delta ^ 3 :=
        mul_le_mul_of_nonneg_right hs (by positivity)
      _ = _ := by rw [mul_pow, mul_pow, mul_pow, hroot]; field_simp; ring
  have hb2 : 16 * B * m * C2 * delta ^ 2 ≤ Delta * ell := by
    calc
      _ = (16 * B * C2) * (m * delta ^ 2) := by ring
      _ ≤ (16 * B * C2) * (3 * c * Delta * ell) :=
        mul_le_mul_of_nonneg_left hm1 (by positivity)
      _ = (48 * c * B * C2) * (Delta * ell) := by ring
      _ ≤ 1 * (Delta * ell) := mul_le_mul_of_nonneg_right hc.2.1 (by positivity)
      _ = _ := one_mul _
  have hb3 : 64 * B ^ 2 * m ^ 2 * C3 * delta ^ 3 ≤ Delta ^ 2 * rho := by
    calc
      _ = (64 * B ^ 2 * C3) * (m ^ 2 * delta ^ 3) := by ring
      _ ≤ (64 * B ^ 2 * C3) * (9 * c ^ 2 * Delta ^ 2 * rho) :=
        mul_le_mul_of_nonneg_left hm2 (by positivity)
      _ = (576 * c ^ 2 * B ^ 2 * C3) * (Delta ^ 2 * rho) := by ring
      _ ≤ 1 * (Delta ^ 2 * rho) := mul_le_mul_of_nonneg_right hc.2.2 (by positivity)
      _ = _ := one_mul _
  change 0 < Delta / (B * m) ∧ 0 < Delta / (B * m) / (4 * delta) ∧ _
  refine ⟨by positivity, by positivity, ?_, ?_, ?_, ?_⟩
  · field_simp
  · field_simp
  · have he : Delta / (B * m) / (Delta / (B * m) / (4 * delta)) ^ 2 * C2 =
        (16 * B * m * C2 * delta ^ 2) / Delta := by field_simp; ring
    rw [he]
    exact (div_le_iff₀ hDelta).mpr (by simpa only [mul_comm ell Delta] using hb2)
  · have he : Delta / (B * m) / (Delta / (B * m) / (4 * delta)) ^ 3 * C3 =
        (64 * B ^ 2 * m ^ 2 * C3 * delta ^ 3) / Delta ^ 2 := by field_simp; ring
    rw [he]
    exact (div_le_iff₀ (pow_pos hDelta 2)).mpr (by simpa only [mul_comm rho (Delta ^ 2)] using hb3)

end
end FangqingSingleLowerNormalizationScalars
end

section
-- Source component: SingleLowerDimensionBudget.lean

namespace FangqingSingleLowerDimensionBudget

noncomputable section

def dimension (CR : ℝ) (m : ℕ) : ℕ :=
  m + Nat.ceil (128 * CR ^ 2 * (m : ℝ) ^ 2 * Real.log (12 * (m : ℝ) ^ 2))

theorem literal_haar_dimension_reserve (CR : ℝ) (hCR : 0 < CR) (m N : ℕ)
    (hm : 1 ≤ m) (hN : N + 1 ≤ m) :
    m ≤ dimension CR m ∧
      2 * (2 * (CR * Real.sqrt m)) ^ 2 / (1 / 4 : ℝ) ^ 2 *
        Real.log ((2 * 1 * (N + 1) * m) / (1 / 6 : ℝ)) ≤
          ((dimension CR m - m : ℕ) : ℝ) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith only [hm1]
  have hNm : (N : ℝ) + 1 ≤ m := by exact_mod_cast hN
  have hlog0 : 0 ≤ Real.log (12 * (m : ℝ) ^ 2) :=
    Real.log_nonneg (by nlinarith only [hm1])
  have hlog : Real.log ((2 * 1 * (N + 1) * m) / (1 / 6 : ℝ)) ≤
      Real.log (12 * (m : ℝ) ^ 2) := by
    apply Real.log_le_log (by positivity)
    nlinarith only [hNm, hm0]
  have hfactor : 2 * (2 * (CR * Real.sqrt m)) ^ 2 / (1 / 4 : ℝ) ^ 2 =
      128 * CR ^ 2 * m := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hm0.le]
    ring
  refine ⟨by unfold dimension; omega, ?_⟩
  unfold dimension
  rw [Nat.add_sub_cancel_left, hfactor]
  calc
    _ ≤ (128 * CR ^ 2 * m) * Real.log (12 * (m : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ ≤ 128 * CR ^ 2 * (m : ℝ) ^ 2 * Real.log (12 * (m : ℝ) ^ 2) := by
      have hh : (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith only [hm1]
      have h := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 128 * CR ^ 2)
      exact mul_le_mul_of_nonneg_right h hlog0
    _ ≤ _ := Nat.le_ceil _

theorem literal_dimension_real_bound (CR : ℝ) (m : ℕ) :
    (dimension CR m : ℝ) ≤ (m : ℝ) +
      128 * CR ^ 2 * (m : ℝ) ^ 2 * Real.log (12 * (m : ℝ) ^ 2) + 1 := by
  let A := 128 * CR ^ 2 * (m : ℝ) ^ 2 * Real.log (12 * (m : ℝ) ^ 2)
  have hc := Nat.ceil_le_floor_add_one A
  have hc' : (Nat.ceil A : ℝ) ≤ (Nat.floor A : ℝ) + 1 := by exact_mod_cast hc
  by_cases hm : m = 0
  · subst m
    norm_num [dimension]
  · have hA : 0 ≤ A := by
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
      have hl : 0 ≤ Real.log (12 * (m : ℝ) ^ 2) := Real.log_nonneg (by nlinarith only [hm1])
      positivity
    have hf := Nat.floor_le hA
    unfold dimension
    push_cast
    change (m : ℝ) + (Nat.ceil A : ℝ) ≤ m + A + 1
    linarith only [hc', hf]

theorem dimension_is_order_T_squared_log_T (CR T : ℝ) (hT : 2 ≤ T) (m : ℕ)
    (hm : 1 ≤ m) (hmT : (m : ℝ) ≤ 3 * T) :
    (dimension CR m : ℝ) ≤ (300000 * (CR ^ 2 + 1)) * T ^ 2 * Real.log T := by
  have hTp : 0 < T := by linarith only [hT]
  have hT0 : 0 ≤ T := hTp.le
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith only [hm1]
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hlogT : (1 / 2 : ℝ) ≤ Real.log T :=
    hlog2.trans (Real.log_le_log (by norm_num) hT)
  have hlog108 : Real.log 108 ≤ (107 : ℝ) := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 108)
    linarith only [hh]
  have harg : 12 * (m : ℝ) ^ 2 ≤ 108 * T ^ 2 := by
    have hh := pow_le_pow_left₀ hm0.le hmT 2
    nlinarith only [hh]
  have hlog : Real.log (12 * (m : ℝ) ^ 2) ≤ 216 * Real.log T := by
    calc
      _ ≤ Real.log (108 * T ^ 2) := Real.log_le_log (by positivity) harg
      _ = Real.log 108 + 2 * Real.log T := by
        rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hTp.ne'), Real.log_pow]
        norm_num
      _ ≤ _ := by linarith only [hlog108, hlogT]
  have hm2 : (m : ℝ) ^ 2 ≤ 9 * T ^ 2 := by
    have hh := pow_le_pow_left₀ hm0.le hmT 2
    nlinarith only [hh]
  have hbound := literal_dimension_real_bound CR m
  have hA : 128 * CR ^ 2 * (m : ℝ) ^ 2 * Real.log (12 * (m : ℝ) ^ 2) ≤
      248832 * CR ^ 2 * T ^ 2 * Real.log T := by
    calc
      _ ≤ 128 * CR ^ 2 * (9 * T ^ 2) * (216 * Real.log T) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hm2 (by positivity)) hlog
          (Real.log_nonneg (by nlinarith only [hm1])) (by positivity)
      _ = _ := by ring
  have hpoly : (m : ℝ) + 1 ≤ 8 * T ^ 2 * Real.log T := by
    have ht2 : T ≤ T ^ 2 := by nlinarith only [hT]
    have hs : (1 : ℝ) ≤ T ^ 2 := by nlinarith only [hT]
    have hh := mul_le_mul_of_nonneg_left hlogT (by positivity : 0 ≤ 8 * T ^ 2)
    nlinarith only [hmT, ht2, hs, hh]
  have hroom : (248832 * CR ^ 2 + 8) * T ^ 2 * Real.log T ≤
      (300000 * (CR ^ 2 + 1)) * T ^ 2 * Real.log T := by
    have hc : 248832 * CR ^ 2 + 8 ≤ 300000 * (CR ^ 2 + 1) := by
      nlinarith only [sq_nonneg CR]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (sq_nonneg T)) (by linarith only [hlogT])
  nlinarith only [hbound, hA, hpoly, hroom]

end
end FangqingSingleLowerDimensionBudget
end

section
-- Source component: SingleLowerOriginalParameters.lean

namespace FangqingSingleLowerOriginalParameters

open FangqingSingleLowerNormalizationScalars FangqingSingleLowerDimensionBudget

noncomputable section

def originalT (B C2 C3 ell rho delta Delta : ℝ) : ℝ :=
  universalRateConstant B C2 C3 * Delta *
    min (ell * delta ^ (-2 : ℝ)) (Real.sqrt rho * delta ^ (-(3 / 2 : ℝ)))

theorem originalT_eq_normalized_target (B C2 C3 ell rho delta Delta : ℝ)
    (hrho : 0 ≤ rho) (hdelta : 0 < delta) :
    originalT B C2 C3 ell rho delta Delta = targetLength B C2 C3 ell rho delta Delta := by
  unfold originalT targetLength
  rw [exact_original_two_smoothness_rate ell rho delta hrho hdelta]

theorem actual_original_rounded_parameters (B C2 C3 CR ell rho delta Delta : ℝ)
    (hB : 1 ≤ B) (hC2 : 0 ≤ C2) (hC3 : 0 ≤ C3) (hCR : 0 < CR)
    (hell : 0 < ell) (hrho : 0 < rho) (hdelta : 0 < delta) (hDelta : 0 < Delta)
    (hT : 2 ≤ originalT B C2 C3 ell rho delta Delta) :
    let T := originalT B C2 C3 ell rho delta Delta
    let n := Nat.ceil T
    let m := n + 1
    let d := dimension CR m
    let amplitude := Delta / (B * m)
    let scale := amplitude / (4 * delta)
    let R := CR * Real.sqrt m
    0 < amplitude ∧ 0 < scale ∧ 0 < R ∧ m ≤ d ∧
      amplitude * B * m = Delta ∧ amplitude / scale = 4 * delta ∧
      amplitude / scale ^ 2 * C2 ≤ ell ∧ amplitude / scale ^ 3 * C3 ≤ rho ∧
      (d : ℝ) ≤ (300000 * (CR ^ 2 + 1)) * T ^ 2 * Real.log T ∧
      ∀ N : ℕ, (N : ℝ) < T → N ≤ n ∧
        2 * (2 * R) ^ 2 / (1 / 4 : ℝ) ^ 2 *
          Real.log ((2 * 1 * (N + 1) * m) / (1 / 6 : ℝ)) ≤ ((d - m : ℕ) : ℝ) := by
  let T := originalT B C2 C3 ell rho delta Delta
  let n := Nat.ceil T
  let m := n + 1
  have hT2 : 2 ≤ T := hT
  have hT1 : 1 ≤ T := by linarith only [hT2]
  have heq := originalT_eq_normalized_target B C2 C3 ell rho delta Delta hrho.le hdelta
  have hround := rounded_chain_length T hT1
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hnorm := simultaneous_two_smoothness_normalization B C2 C3 ell rho delta Delta
    hB hC2 hC3 hell hrho hdelta hDelta (by rw [← heq]; exact hT1)
  rw [← heq] at hnorm
  have hd := literal_haar_dimension_reserve CR hCR m 0 hm (by omega)
  refine ⟨hnorm.1, hnorm.2.1, by positivity, hd.1, hnorm.2.2.1,
    hnorm.2.2.2.1, hnorm.2.2.2.2.1, hnorm.2.2.2.2.2, ?_, ?_⟩
  · exact dimension_is_order_T_squared_log_T CR T hT2 m hm hround.2.1
  · intro N hN
    have hn : N ≤ n := hround.2.2 N hN
    exact ⟨hn, (literal_haar_dimension_reserve CR hCR m N hm (by dsimp [m]; omega)).2⟩

end
end FangqingSingleLowerOriginalParameters
end

section
-- Source component: SingleLowerFixedFunctionExecution.lean

namespace FangqingSingleLowerFixedFunctionExecution

open OriginalPrefixOracleReplay FangqingSingleLowerActualOracleProgram
  FangqingSingleLowerAllDerivativeOracle FangqingSingleLowerOracleRescaling

noncomputable section

variable {Seed E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def outputOnFunction (n N : ℕ) (q : Query Seed (Response E) E)
    (out : Seed → State (Response E) → E) (f : E → ℝ) (seed : Seed) : E :=
  out seed (run q (grantEveryResponse n) (familyReply (fun _ : Fin (n + 1) → E => f)) N seed 0)

theorem actual_run_is_the_run_of_one_fixed_function (n N : ℕ)
    (f : (Fin (n + 1) → E) → E → ℝ) (q : Query Seed (Response E) E)
    (seed : Seed) (V : Fin (n + 1) → E) :
    run q (grantEveryResponse n) (familyReply f) N seed V =
      run q (grantEveryResponse n) (familyReply (fun _ : Fin (n + 1) → E => f V)) N seed 0 := by
  induction N with
  | zero => rfl
  | succ N ih =>
      simp only [run]
      rw [ih]
      rfl

theorem actual_output_is_the_output_on_one_fixed_function (n N : ℕ)
    (f : (Fin (n + 1) → E) → E → ℝ) (q : Query Seed (Response E) E)
    (out : Seed → State (Response E) → E) (seed : Seed) (V : Fin (n + 1) → E) :
    out seed (run q (grantEveryResponse n) (familyReply f) N seed V) =
      outputOnFunction n N q out (f V) seed :=
  congrArg (out seed) (actual_run_is_the_run_of_one_fixed_function n N f q seed V)

end
end FangqingSingleLowerFixedFunctionExecution
end

section
-- Source component: SingleLowerOriginalTheorem.lean

open MeasureTheory
open scoped ContDiff ENNReal

namespace FangqingSingleLowerOriginalTheorem

open FangqingSingleLowerNormalizedLower FangqingSingleLowerNormalizationScalars
  FangqingSingleLowerDimensionBudget FangqingSingleLowerOriginalParameters
  FangqingSingleLowerPhysicalGradient FangqingSingleLowerLocalizedGap
  FangqingSingleLowerAllDerivativeOracle FangqingSingleLowerActualOracleProgram
  FangqingSingleLowerFixedHaarWorld FangqingSingleLowerOracleRescaling
  FangqingSingleLowerFixedFunctionExecution OriginalPrefixOracleReplay
  FangqingAdaptiveHaarProduct FangqingAdaptiveHaarConcrete

noncomputable section

universe v

theorem gradient_norm_is_derivative_norm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : E → ℝ) (x : E) :
    ‖gradient f x‖ = ‖fderiv ℝ f x‖ :=
  (InnerProductSpace.toDual ℝ E).symm.norm_map _

/-- The original worst-case oracle convention: one fixed legal function is
    selected against each measurable randomized algorithm, independently of its seed. -/
theorem original_contextual_minimax_all_derivative_lower :
    ∃ c Cdim : ℝ, 0 < c ∧ 0 < Cdim ∧
      ∀ ell rho delta Delta : ℝ, 0 < ell → 0 < rho → 0 < delta → 0 < Delta →
      let T := c * Delta *
        min (ell * delta ^ (-2 : ℝ)) (Real.sqrt rho * delta ^ (-(3 / 2 : ℝ)))
      2 ≤ T → ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ Cdim * T ^ 2 * Real.log T ∧
      ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
        [MeasurableSpace (Response E)] [BorelSpace (Response E)],
      ∀ (b : OrthonormalBasis (Fin d) ℝ E),
      ∀ (Seed : Type v) [MeasurableSpace Seed] (seeds : Measure Seed) [IsProbabilityMeasure seeds],
      ∀ N : ℕ, (N : ℝ) < T → ∀ (q : Query Seed (Response E) E),
        (∀ t, Measurable (fun x : Seed × State (Response E) => q t x.1 x.2)) →
      ∀ (out : Seed → State (Response E) → E),
        Measurable (fun x : Seed × State (Response E) => out x.1 x.2) →
      ∃ f : E → ℝ, ContDiff ℝ ∞ f ∧ f 0 - sInf (Set.range f) ≤ Delta ∧
        (∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ ell) ∧
        (∀ x y, ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤ rho * ‖x - y‖) ∧
        (2 / 3 : ℝ≥0∞) ≤ seeds {seed | delta <
          ‖gradient f (outputOnFunction (Nat.ceil T) N q out f seed)‖} := by
  obtain ⟨CR, C2, C3, hCR, hC2, hC3, hnormalized⟩ :=
    actual_universal_normalized_all_derivative_lower_family.{0, v}
  let B : ℝ := 4 * Real.pi
  have hB : 1 ≤ B := by dsimp [B]; linarith only [Real.pi_gt_three]
  let c := universalRateConstant B C2 C3
  have hc : 0 < c := (universal_budget_margins B C2 C3 hB (zero_le_one.trans hC2)
    (zero_le_one.trans hC3)).1
  refine ⟨c, 300000 * (CR ^ 2 + 1), hc, by positivity, ?_⟩
  intro ell rho delta Delta hell hrho hdelta hDelta T hT
  let n := Nat.ceil T
  let m := n + 1
  let d := dimension CR m
  let alpha : ℝ := Delta / (B * m)
  let beta : ℝ := alpha / (4 * delta)
  let R := CR * Real.sqrt m
  have hp := actual_original_rounded_parameters B C2 C3 CR ell rho delta Delta hB
    (zero_le_one.trans hC2) (zero_le_one.trans hC3) (zero_lt_one.trans_le hCR)
    hell hrho hdelta hDelta hT
  have hT_eq : originalT B C2 C3 ell rho delta Delta = T := rfl
  rw [hT_eq] at hp
  rcases hp with ⟨ha, hb, hR, hmd, hAlphaBudget, hratio, hessBudget, thirdBudget, hdim, hNbound⟩
  change 0 < alpha at ha
  change 0 < beta at hb
  change m ≤ d at hmd
  change alpha * B * m = Delta at hAlphaBudget
  have hdp : 0 < d := by
    have hm : 0 < m := by dsimp [m]; omega
    omega
  refine ⟨d, hdp, hdim, ?_⟩
  intro E inst inst' inst'' inst''' instM instB instN instResp instBResp
    b Seed instSeed seeds instProb N hN q hq out hout
  obtain ⟨hn, hHaarBudget⟩ := hNbound N hN
  change N ≤ n at hn
  have hHaarBudget' : 2 * (2 * R) ^ 2 / (1 / 4 : ℝ) ^ 2 *
      Real.log ((2 * 1 * (N + 1) * (n + 1)) / (1 / 6 : ℝ)) ≤ ((d - (n + 1) : ℕ) : ℝ) := by
    simpa only [R, m, Nat.cast_add, Nat.cast_one] using hHaarBudget
  have hqb := baseQuery_measurable alpha beta q hq
  have hob := baseOutput_measurable alpha beta out hout
  obtain ⟨g, hSmooth, hGap, hHess, hHessLip, hProb⟩ :=
    hnormalized E Seed seeds n N d hn b hmd (baseQuery alpha beta q) hqb
      (baseOutput alpha beta out) hob hHaarBudget'
  let family : (Fin (n + 1) → E) → E → ℝ :=
    localizedChain FangqingPublicShellProfiles.theta R n
  let V : Fin (n + 1) → E := frame (basisPrefix b hmd) g
  let f := scaledFunction alpha beta (family V)
  have hFamily : ∀ V, ContDiff ℝ ∞ (family V) :=
    fun V => actual_localized_chain_smooth _ FangqingPublicShellProfiles.theta_smooth R n V
  have hbaseGap : family V 0 - sInf (Set.range (family V)) ≤ B * m := by
    simpa only [family, V, B, R, m, Nat.cast_add, Nat.cast_one] using hGap
  have hGapScale : alpha * (B * m) ≤ Delta := by nlinarith only [hAlphaBudget]
  have hscaled := scaled_actual_class_and_initial_gap alpha beta C2 C3 (B * m) ell rho Delta
    ha hb (family V) hSmooth hHess hHessLip hbaseGap hessBudget thirdBudget
      hGapScale
  have hbaseProb : (2 / 3 : ℝ≥0∞) ≤ seeds {seed | (9 / 10 : ℝ) ≤
      ‖fderiv ℝ (family V) (baseOutput alpha beta out seed
        (run (baseQuery alpha beta q) (grantEveryResponse n) (familyReply family) N seed V))‖} := by
    have hReplyEq : (FangqingSingleLowerActualOracleProgram.reply FangqingPublicShellProfiles.theta R n :
        Reply Seed E (Response E) E (n + 1)) = familyReply family := rfl
    change (2 / 3 : ℝ≥0∞) ≤ seeds {seed | (9 / 10 : ℝ) ≤
      ‖fderiv ℝ (family V) (baseOutput alpha beta out seed
        (run (baseQuery alpha beta q) (grantEveryResponse n)
          (FangqingSingleLowerActualOracleProgram.reply FangqingPublicShellProfiles.theta R n) N seed V))‖} at hProb
    rw [hReplyEq] at hProb
    exact hProb
  have hprob := hbaseProb.trans
    (actual_scaled_program_failure_measure seeds alpha beta delta ha hb hdelta hratio n family hFamily q out N V)
  have hfixed (seed : Seed) : out seed
      (run q (grantEveryResponse n) (familyReply (scaledFamily alpha beta family)) N seed V) =
        outputOnFunction n N q out f seed :=
    actual_output_is_the_output_on_one_fixed_function n N (scaledFamily alpha beta family) q out seed V
  refine ⟨f, hscaled.1, hscaled.2.1, hscaled.2.2.1, hscaled.2.2.2, ?_⟩
  change (2 / 3 : ℝ≥0∞) ≤ seeds {seed | delta < ‖fderiv ℝ f
    (out seed (run q (grantEveryResponse n) (familyReply (scaledFamily alpha beta family)) N seed V))‖} at hprob
  simp_rw [hfixed] at hprob
  simpa only [gradient_norm_is_derivative_norm] using hprob

end
end FangqingSingleLowerOriginalTheorem
end

section
-- Source component: SingleLowerAlgorithmMeasurability.lean

open MeasureTheory
open scoped ContDiff ENNReal

namespace FangqingSingleLowerAlgorithmMeasurability

open OriginalPrefixOracleReplay FangqingSingleLowerActualOracleProgram
  FangqingSingleLowerAllDerivativeOracle FangqingSingleLowerOracleRescaling
  FangqingSingleLowerFixedFunctionExecution

noncomputable section
set_option maxHeartbeats 3500000

variable {Seed E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace Seed] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (Response E)] [BorelSpace (Response E)]

theorem fixed_full_oracle_reply_measurable (n : ℕ) (f : E → ℝ)
    (hf : ContDiff ℝ ∞ f) (t : ℕ) :
    Measurable (fun x : Seed × State (Response E) × ℕ × (Fin (n + 1) → E) × E =>
      familyReply (fun _ : Fin (n + 1) → E => f) t x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) := by
  have hc : Continuous (fun p : (Fin (n + 1) → E) × E => allDerivativeOracle f p.2) :=
    complete_infinite_oracle_family_continuous (fun _ : Fin (n + 1) → E => f)
      (hf.comp contDiff_snd)
  exact hc.measurable.comp
    ((measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))).prodMk
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))))

theorem actual_fixed_function_output_measurable (n N : ℕ)
    (q : Query Seed (Response E) E)
    (hq : ∀ t, Measurable (fun x : Seed × State (Response E) => q t x.1 x.2))
    (out : Seed → State (Response E) → E)
    (hout : Measurable (fun x : Seed × State (Response E) => out x.1 x.2))
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f) :
    Measurable (outputOnFunction n N q out f) := by
  have hrun := run_measurable q (grantEveryResponse n)
    (familyReply (fun _ : Fin (n + 1) → E => f)) hq (fun _ => measurable_const)
    (fixed_full_oracle_reply_measurable n f hf) N
  exact hout.comp (measurable_id.prodMk
    (hrun.comp (measurable_id.prodMk measurable_const)))

theorem actual_fixed_function_gradient_norm_measurable (n N : ℕ)
    (q : Query Seed (Response E) E)
    (hq : ∀ t, Measurable (fun x : Seed × State (Response E) => q t x.1 x.2))
    (out : Seed → State (Response E) → E)
    (hout : Measurable (fun x : Seed × State (Response E) => out x.1 x.2))
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f) :
    Measurable (fun seed => ‖gradient f (outputOnFunction n N q out f seed)‖) := by
  have h2 : ContDiff ℝ 2 f := hf.of_le (by decide)
  have hd : Continuous (fderiv ℝ f) := (h2.fderiv_right (m := 1) (by norm_num)).continuous
  have hg : Continuous (gradient f) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp hd
  exact hg.norm.measurable.comp (actual_fixed_function_output_measurable n N q hq out hout f hf)

theorem actual_fixed_function_stationarity_event_measurable (n N : ℕ)
    (q : Query Seed (Response E) E)
    (hq : ∀ t, Measurable (fun x : Seed × State (Response E) => q t x.1 x.2))
    (out : Seed → State (Response E) → E)
    (hout : Measurable (fun x : Seed × State (Response E) => out x.1 x.2))
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (delta : ℝ) :
    MeasurableSet {seed | ‖gradient f (outputOnFunction n N q out f seed)‖ ≤ delta} :=
  measurableSet_le (actual_fixed_function_gradient_norm_measurable n N q hq out hout f hf)
    measurable_const

theorem actual_fixed_function_failure_event_measurable (n N : ℕ)
    (q : Query Seed (Response E) E)
    (hq : ∀ t, Measurable (fun x : Seed × State (Response E) => q t x.1 x.2))
    (out : Seed → State (Response E) → E)
    (hout : Measurable (fun x : Seed × State (Response E) => out x.1 x.2))
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (delta : ℝ) :
    MeasurableSet {seed | delta < ‖gradient f (outputOnFunction n N q out f seed)‖} :=
  measurableSet_lt measurable_const
    (actual_fixed_function_gradient_norm_measurable n N q hq out hout f hf)

/-- Complementation is applied to actual measurable events of one fixed function. -/
theorem actual_failure_probability_bounds_success (seeds : Measure Seed)
    [IsProbabilityMeasure seeds] (n N : ℕ)
    (q : Query Seed (Response E) E)
    (hq : ∀ t, Measurable (fun x : Seed × State (Response E) => q t x.1 x.2))
    (out : Seed → State (Response E) → E)
    (hout : Measurable (fun x : Seed × State (Response E) => out x.1 x.2))
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (delta : ℝ)
    (hfail : (2 / 3 : ℝ≥0∞) ≤ seeds
      {seed | delta < ‖gradient f (outputOnFunction n N q out f seed)‖}) :
    seeds {seed | ‖gradient f (outputOnFunction n N q out f seed)‖ ≤ delta} ≤ (1 / 3 : ℝ≥0∞) := by
  have hm := actual_fixed_function_failure_event_measurable n N q hq out hout f hf delta
  have heq : {seed | ‖gradient f (outputOnFunction n N q out f seed)‖ ≤ delta} =
      {seed | delta < ‖gradient f (outputOnFunction n N q out f seed)‖}ᶜ := by
    ext seed
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]
  rw [heq, measure_compl hm (measure_ne_top seeds _), measure_univ]
  calc
    _ ≤ 1 - (2 / 3 : ℝ≥0∞) := tsub_le_tsub_left hfail _
    _ = (1 / 3 : ℝ≥0∞) := by
      have htwo : ENNReal.ofReal (2 / 3 : ℝ) = (2 / 3 : ℝ≥0∞) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]
        norm_num
      calc
        _ = ENNReal.ofReal 1 - ENNReal.ofReal (2 / 3 : ℝ) := by rw [htwo]; norm_num
        _ = ENNReal.ofReal (1 - (2 / 3 : ℝ)) :=
          (ENNReal.ofReal_sub 1 (by norm_num : (0 : ℝ) ≤ 2 / 3)).symm
        _ = (1 / 3 : ℝ≥0∞) := by
          norm_num [ENNReal.ofReal_div_of_pos]

end
end FangqingSingleLowerAlgorithmMeasurability

namespace FangqingSingleLowerCanonicalEuclidean

open FangqingSingleLowerActualOracleProgram

noncomputable section

def canonicalBasis (d : ℕ) : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) :=
  EuclideanSpace.basisFun (Fin d) ℝ

theorem canonical_euclidean_nontrivial (d : ℕ) (hd : 0 < d) :
    Nontrivial (EuclideanSpace ℝ (Fin d)) := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  infer_instance

abbrev canonicalResponseMeasurableSpace (d : ℕ) :
    MeasurableSpace (Response (EuclideanSpace ℝ (Fin d))) := borel _

theorem canonical_response_borel (d : ℕ) :
    letI : MeasurableSpace (Response (EuclideanSpace ℝ (Fin d))) := canonicalResponseMeasurableSpace d
    BorelSpace (Response (EuclideanSpace ℝ (Fin d))) := by
  letI : MeasurableSpace (Response (EuclideanSpace ℝ (Fin d))) := canonicalResponseMeasurableSpace d
  exact ⟨rfl⟩

end
end FangqingSingleLowerCanonicalEuclidean
end

section
-- Source component: SingleLowerEuclideanOriginalTheorem.lean

open MeasureTheory
open scoped ContDiff ENNReal

namespace FangqingSingleLowerEuclideanOriginalTheorem

open FangqingSingleLowerOriginalTheorem FangqingSingleLowerActualOracleProgram
  FangqingSingleLowerFixedFunctionExecution FangqingSingleLowerAlgorithmMeasurability
  FangqingSingleLowerCanonicalEuclidean OriginalPrefixOracleReplay

noncomputable section

universe v

theorem original_euclidean_all_derivative_minimax_lower :
    ∃ c Cdim : ℝ, 0 < c ∧ 0 < Cdim ∧
      ∀ ell rho delta Delta : ℝ, 0 < ell → 0 < rho → 0 < delta → 0 < Delta →
      let T := c * Delta *
        min (ell * delta ^ (-2 : ℝ)) (Real.sqrt rho * delta ^ (-(3 / 2 : ℝ)))
      2 ≤ T → ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ Cdim * T ^ 2 * Real.log T ∧
      letI : MeasurableSpace (Response (EuclideanSpace ℝ (Fin d))) := canonicalResponseMeasurableSpace d
      ∀ (Seed : Type v) [MeasurableSpace Seed] (seeds : Measure Seed) [IsProbabilityMeasure seeds],
      ∀ N : ℕ, (N : ℝ) < T → ∀ (q : Query Seed (Response (EuclideanSpace ℝ (Fin d))) (EuclideanSpace ℝ (Fin d))),
        (∀ t, Measurable (fun x : Seed × State (Response (EuclideanSpace ℝ (Fin d))) => q t x.1 x.2)) →
      ∀ (out : Seed → State (Response (EuclideanSpace ℝ (Fin d))) → EuclideanSpace ℝ (Fin d)),
        Measurable (fun x : Seed × State (Response (EuclideanSpace ℝ (Fin d))) => out x.1 x.2) →
      ∃ f : EuclideanSpace ℝ (Fin d) → ℝ,
        ContDiff ℝ ∞ f ∧ f 0 - sInf (Set.range f) ≤ Delta ∧
        (∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ ell) ∧
        (∀ x y, ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤ rho * ‖x - y‖) ∧
        seeds {seed | ‖gradient f (outputOnFunction (Nat.ceil T) N q out f seed)‖ ≤ delta} ≤
          (1 / 3 : ℝ≥0∞) := by
  obtain ⟨c, Cdim, hc, hCdim, hAll⟩ := original_contextual_minimax_all_derivative_lower.{v}
  refine ⟨c, Cdim, hc, hCdim, ?_⟩
  intro ell rho delta Delta hell hrho hdelta hDelta T hT
  obtain ⟨d, hd, hdim, hLower⟩ := hAll ell rho delta Delta hell hrho hdelta hDelta hT
  refine ⟨d, hd, hdim, ?_⟩
  letI : Nontrivial (EuclideanSpace ℝ (Fin d)) := canonical_euclidean_nontrivial d hd
  letI : MeasurableSpace (Response (EuclideanSpace ℝ (Fin d))) := canonicalResponseMeasurableSpace d
  letI : BorelSpace (Response (EuclideanSpace ℝ (Fin d))) := canonical_response_borel d
  intro Seed instSeed seeds instProb N hN q hq out hout
  obtain ⟨f, hf, hgap, hHess, hHessLip, hfail⟩ :=
    hLower (EuclideanSpace ℝ (Fin d)) (canonicalBasis d) Seed seeds N hN q hq out hout
  exact ⟨f, hf, hgap, hHess, hHessLip,
    actual_failure_probability_bounds_success seeds (Nat.ceil T) N q hq out hout f hf delta hfail⟩

end
end FangqingSingleLowerEuclideanOriginalTheorem
end

section
-- Source component: SingleLowerEarlyStopPadding.lean

open MeasureTheory

namespace FangqingSingleLowerEarlyStopPadding

open OriginalPrefixOracleReplay FangqingSingleLowerActualOracleProgram
  FangqingSingleLowerAllDerivativeOracle FangqingSingleLowerOracleRescaling
  FangqingSingleLowerFixedFunctionExecution

noncomputable section
set_option maxHeartbeats 4000000

structure Machine (Seed S E A : Type*) where
  init : Seed → S
  stop : S → Bool
  query : S → E
  update : S × A → S
  output : S → E

variable {Seed S E A : Type*}

def simulate (M : Machine Seed S E A) : ℕ → Seed → (ℕ → A) → S
  | 0, seed, _ => M.init seed
  | n + 1, seed, h =>
      let s := simulate M n seed h
      if M.stop s = true then s else M.update (s, h n)

def earlyRun (M : Machine Seed S E A) (oracle : E → A) : ℕ → Seed → S
  | 0, seed => M.init seed
  | n + 1, seed =>
      let s := earlyRun M oracle n seed
      if M.stop s = true then s else M.update (s, oracle (M.query s))

/-- Actual original-machine oracle requests, excluding post-stop padding. -/
def paidCalls (M : Machine Seed S E A) (oracle : E → A) : ℕ → Seed → ℕ
  | 0, _ => 0
  | n + 1, seed => paidCalls M oracle n seed +
      if M.stop (earlyRun M oracle n seed) = true then 0 else 1

def paddedQuery [Zero E] (M : Machine Seed S E A) : Query Seed A E :=
  fun n seed st =>
    let s := simulate M n seed st.2
    if M.stop s = true then 0 else M.query s

def paddedOutput (M : Machine Seed S E A) (N : ℕ) : Seed → State A → E :=
  fun seed st => M.output (simulate M N seed st.2)

theorem simulate_depends_only_on_past (M : Machine Seed S E A) (n : ℕ)
    (seed : Seed) (h k : ℕ → A) (hpast : ∀ i < n, h i = k i) :
    simulate M n seed h = simulate M n seed k := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hs := ih (fun i hi => hpast i (by omega))
      simp only [simulate, hs, hpast n (by omega)]

theorem simulate_unchanged_by_next_reply_update (M : Machine Seed S E A) (n : ℕ)
    (seed : Seed) (h : ℕ → A) (a : A) :
    simulate M n seed (Function.update h n a) = simulate M n seed h := by
  apply simulate_depends_only_on_past
  intro i hi
  simp only [Function.update_apply, ne_of_lt hi, if_false]

theorem early_state_frozen_after_stop (M : Machine Seed S E A) (oracle : E → A)
    (n k : ℕ) (seed : Seed) (hstop : M.stop (earlyRun M oracle n seed) = true) :
    earlyRun M oracle (n + k) seed = earlyRun M oracle n seed := by
  induction k with
  | zero => simp only [Nat.add_zero]
  | succ k ih =>
      rw [Nat.add_succ, earlyRun, ih]
      simp only [hstop, if_true]

theorem actual_machine_paid_calls_frozen_after_stop (M : Machine Seed S E A) (oracle : E → A)
    (n k : ℕ) (seed : Seed) (hstop : M.stop (earlyRun M oracle n seed) = true) :
    paidCalls M oracle (n + k) seed = paidCalls M oracle n seed := by
  induction k with
  | zero => simp only [Nat.add_zero]
  | succ k ih =>
      rw [Nat.add_succ, paidCalls, early_state_frozen_after_stop M oracle n k seed hstop, ih]
      simp only [hstop, if_true, Nat.add_zero]

theorem actual_machine_paid_calls_le_horizon (M : Machine Seed S E A) (oracle : E → A)
    (N : ℕ) (seed : Seed) : paidCalls M oracle N seed ≤ N := by
  induction N with
  | zero => rfl
  | succ N ih =>
      simp only [paidCalls]
      split_ifs <;> omega

section BorelMachine

variable [MeasurableSpace Seed] [MeasurableSpace S] [MeasurableSpace E] [MeasurableSpace A]

structure BorelMachine (M : Machine Seed S E A) : Prop where
  init : Measurable M.init
  stop : Measurable M.stop
  query : Measurable M.query
  update : Measurable M.update
  output : Measurable M.output

theorem simulate_measurable (M : Machine Seed S E A) (hM : BorelMachine M) (n : ℕ) :
    Measurable (fun x : Seed × (ℕ → A) => simulate M n x.1 x.2) := by
  induction n with
  | zero => exact hM.init.comp measurable_fst
  | succ n ih =>
      exact Measurable.ite ((hM.stop.comp ih) (measurableSet_singleton true)) ih
        (hM.update.comp (ih.prodMk ((measurable_pi_apply n).comp measurable_snd)))

theorem padded_query_measurable [Zero E] (M : Machine Seed S E A) (hM : BorelMachine M)
    (n : ℕ) : Measurable (fun x : Seed × State A => paddedQuery M n x.1 x.2) := by
  have hs : Measurable (fun x : Seed × State A => simulate M n x.1 x.2.2) :=
    (simulate_measurable M hM n).comp
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  exact Measurable.ite ((hM.stop.comp hs) (measurableSet_singleton true)) measurable_const
    (hM.query.comp hs)

theorem padded_output_measurable (M : Machine Seed S E A) (hM : BorelMachine M) (N : ℕ) :
    Measurable (fun x : Seed × State A => paddedOutput M N x.1 x.2) :=
  hM.output.comp ((simulate_measurable M hM N).comp
    (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))

end BorelMachine

section ActualFullOracle

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Genuine padded all-order-oracle execution on one fixed function has
    exactly the same internal state as the original early-stop machine. -/
theorem actual_padded_state_is_original_early_state
    (M : Machine Seed S E (Response E)) (f : E → ℝ) (n N : ℕ) (seed : Seed) :
    simulate M N seed
      (run (paddedQuery M) (grantEveryResponse n)
        (familyReply (fun _ : Fin (n + 1) → E => f)) N seed 0).2 =
      earlyRun M (allDerivativeOracle f) N seed := by
  induction N with
  | zero => rfl
  | succ N ih =>
      let st := run (paddedQuery M) (grantEveryResponse n)
        (familyReply (fun _ : Fin (n + 1) → E => f)) N seed 0
      change simulate M (N + 1) seed (Function.update st.2 N
        (allDerivativeOracle f (paddedQuery M N seed st))) = _
      rw [simulate, simulate_unchanged_by_next_reply_update]
      change simulate M N seed st.2 = earlyRun M (allDerivativeOracle f) N seed at ih
      rw [ih, earlyRun]
      by_cases hstop : M.stop (earlyRun M (allDerivativeOracle f) N seed) = true
      · simp only [hstop, if_true]
      · simp [paddedQuery, ih, hstop, Function.update_self]

theorem actual_padded_output_is_original_early_output
    (M : Machine Seed S E (Response E)) (f : E → ℝ) (n N : ℕ) (seed : Seed) :
    outputOnFunction n N (paddedQuery M) (paddedOutput M N) f seed =
      M.output (earlyRun M (allDerivativeOracle f) N seed) := by
  unfold outputOnFunction paddedOutput
  rw [actual_padded_state_is_original_early_state]

/-- Dummy calls after an actual stop are always at the public zero point. -/
theorem actual_post_stop_padded_query_is_zero
    (M : Machine Seed S E (Response E)) (f : E → ℝ) (n t k : ℕ) (seed : Seed)
    (hstop : M.stop (earlyRun M (allDerivativeOracle f) t seed) = true) :
    paddedQuery M (t + k) seed
      (run (paddedQuery M) (grantEveryResponse n)
        (familyReply (fun _ : Fin (n + 1) → E => f)) (t + k) seed 0) = 0 := by
  simp only [paddedQuery, actual_padded_state_is_original_early_state,
    early_state_frozen_after_stop M (allDerivativeOracle f) t k seed hstop, hstop, if_true]

theorem actual_padded_return_point_is_unchanged_after_stop
    (M : Machine Seed S E (Response E)) (f : E → ℝ) (n t k : ℕ) (seed : Seed)
    (hstop : M.stop (earlyRun M (allDerivativeOracle f) t seed) = true) :
    outputOnFunction n (t + k) (paddedQuery M) (paddedOutput M (t + k)) f seed =
      M.output (earlyRun M (allDerivativeOracle f) t seed) := by
  rw [actual_padded_output_is_original_early_output,
    early_state_frozen_after_stop M (allDerivativeOracle f) t k seed hstop]

theorem actual_padded_return_at_any_bounded_stop
    (M : Machine Seed S E (Response E)) (f : E → ℝ) (n N t : ℕ) (seed : Seed)
    (ht : t ≤ N) (hstop : M.stop (earlyRun M (allDerivativeOracle f) t seed) = true) :
    outputOnFunction n N (paddedQuery M) (paddedOutput M N) f seed =
      M.output (earlyRun M (allDerivativeOracle f) t seed) := by
  have hh := actual_padded_return_point_is_unchanged_after_stop M f n t (N - t) seed hstop
  simpa only [Nat.add_sub_of_le ht] using hh

/-- Complete actual-program adapter: the padded program is Borel, executes
    exactly N paid full-oracle calls, and returns the original machine point.
    Original requests exclude the dummy calls and are bounded by N. -/
theorem actual_borel_machine_padding_interface
    [MeasurableSpace Seed] [MeasurableSpace S] [MeasurableSpace E]
    [MeasurableSpace (Response E)]
    (M : Machine Seed S E (Response E)) (hM : BorelMachine M)
    (f : E → ℝ) (n N : ℕ) :
    (∀ t, Measurable (fun x : Seed × State (Response E) => paddedQuery M t x.1 x.2)) ∧
      Measurable (fun x : Seed × State (Response E) => paddedOutput M N x.1 x.2) ∧
      (∀ seed, outputOnFunction n N (paddedQuery M) (paddedOutput M N) f seed =
        M.output (earlyRun M (allDerivativeOracle f) N seed)) ∧
      (∀ seed, (actualQueryTrace n (fun _ : Fin (n + 1) → E => f)
        (paddedQuery M) N seed 0).length = N) ∧
      (∀ seed, paidCalls M (allDerivativeOracle f) N seed ≤ N) := by
  exact ⟨padded_query_measurable M hM, padded_output_measurable M hM N,
    actual_padded_output_is_original_early_output M f n N,
    fun seed => actualQueryTrace_length n (fun _ : Fin (n + 1) → E => f) (paddedQuery M) N seed 0,
    actual_machine_paid_calls_le_horizon M (allDerivativeOracle f) N⟩

end ActualFullOracle
end
end FangqingSingleLowerEarlyStopPadding
end

section
-- Source component: SingleLowerArbitraryAlgorithmTheorem.lean

open MeasureTheory
open scoped ContDiff ENNReal

namespace FangqingSingleLowerArbitraryAlgorithmTheorem

open FangqingSingleLowerEuclideanOriginalTheorem FangqingSingleLowerActualOracleProgram
  FangqingSingleLowerAllDerivativeOracle FangqingSingleLowerCanonicalEuclidean
  FangqingSingleLowerEarlyStopPadding

noncomputable section

universe v w

/-- Arbitrary measurable state and early stopping are included. A bounded
    algorithm's state is frozen after its actual stop, and the function is
    selected once before drawing its independent random seed. -/
theorem original_arbitrary_measurable_algorithm_minimax_lower :
    ∃ c Cdim : ℝ, 0 < c ∧ 0 < Cdim ∧
      ∀ ell rho delta Delta : ℝ, 0 < ell → 0 < rho → 0 < delta → 0 < Delta →
      let T := c * Delta *
        min (ell * delta ^ (-2 : ℝ)) (Real.sqrt rho * delta ^ (-(3 / 2 : ℝ)))
      2 ≤ T → ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ Cdim * T ^ 2 * Real.log T ∧
      letI : MeasurableSpace (Response (EuclideanSpace ℝ (Fin d))) := canonicalResponseMeasurableSpace d
      ∀ (Seed : Type v) [MeasurableSpace Seed] (seeds : Measure Seed) [IsProbabilityMeasure seeds],
      ∀ (S : Type w) [MeasurableSpace S],
      ∀ (M : Machine Seed S (EuclideanSpace ℝ (Fin d)) (Response (EuclideanSpace ℝ (Fin d)))),
      BorelMachine M → ∀ N : ℕ, (N : ℝ) < T →
      ∃ f : EuclideanSpace ℝ (Fin d) → ℝ,
        ContDiff ℝ ∞ f ∧ f 0 - sInf (Set.range f) ≤ Delta ∧
        (∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ ell) ∧
        (∀ x y, ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤ rho * ‖x - y‖) ∧
        seeds {seed | ‖gradient f (M.output (earlyRun M (allDerivativeOracle f) N seed))‖ ≤ delta} ≤
          (1 / 3 : ℝ≥0∞) := by
  obtain ⟨c, Cdim, hc, hCdim, hAll⟩ := original_euclidean_all_derivative_minimax_lower.{v}
  refine ⟨c, Cdim, hc, hCdim, ?_⟩
  intro ell rho delta Delta hell hrho hdelta hDelta T hT
  obtain ⟨d, hd, hdim, hLower⟩ := hAll ell rho delta Delta hell hrho hdelta hDelta hT
  refine ⟨d, hd, hdim, ?_⟩
  letI : MeasurableSpace (Response (EuclideanSpace ℝ (Fin d))) := canonicalResponseMeasurableSpace d
  intro Seed instSeed seeds instProb S instS M hM N hN
  obtain ⟨f, hf, hgap, hHess, hHessLip, hProb⟩ :=
    hLower Seed seeds N hN (paddedQuery M) (padded_query_measurable M hM)
      (paddedOutput M N) (padded_output_measurable M hM N)
  refine ⟨f, hf, hgap, hHess, hHessLip, ?_⟩
  simpa only [actual_padded_output_is_original_early_output] using hProb

end
end FangqingSingleLowerArbitraryAlgorithmTheorem
end

section
-- Source component: AllDerivativeLiftCoreSnapshotForExecution.lean

namespace AllDerivativeLift

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

noncomputable def center (b : ℝ) (c x : E) : E := b • x + c
noncomputable def lift (F : E → ℝ) (mu b : ℝ) (c x y : E) : ℝ :=
  F y - mu * ‖y - center b c x‖ ^ 2
noncomputable def phi (F : E → ℝ) (mu b : ℝ) (c x : E) : ℝ :=
  sSup (Set.range (lift F mu b c x))
noncomputable def yStar (F : E → ℝ) (mu b : ℝ) (c x : E) : E :=
  Classical.epsilon (fun y => ∀ z, lift F mu b c x z ≤ lift F mu b c x y)

noncomputable def affineDifference (b : ℝ) : JointSliceRegularity.JointSpace E E →L[ℝ] E :=
  WithLp.sndL 2 ℝ E E - b • WithLp.fstL 2 ℝ E E

noncomputable def jointLift (F : E → ℝ) (mu b : ℝ) (c : E)
    (z : JointSliceRegularity.JointSpace E E) : ℝ :=
  F z.snd - mu * ‖affineDifference b z - c‖ ^ 2

theorem jointLift_eq_lift (F : E → ℝ) (mu b : ℝ) (c x y : E) :
    jointLift F mu b c (JointSliceRegularity.point x y) = lift F mu b c x y := by
  rw [JointSliceRegularity.point_eq_toLp]
  change F y - mu * ‖y - b • x - c‖ ^ 2 = F y - mu * ‖y - (b • x + c)‖ ^ 2
  rw [sub_add_eq_sub_sub]

theorem negative_y_strongConvex (F : E → ℝ) (mu b : ℝ) (c : E)
    (hmu : 0 < mu) (hdiff : Differentiable ℝ F)
    (hlip : ∀ y z : E, ‖gradient F y - gradient F z‖ ≤ mu * ‖y - z‖)
    (x : E) : StrongConvexOn (Set.univ : Set E) mu (fun y => -lift F mu b c x y) := by
  apply strongConvexOn_iff_convex.mpr
  apply OriginalSaddleRegularity.convex_of_global_support _
    (fun y => (2 * mu) • (y - center b c x) - gradient F y - mu • y)
  intro y z
  have hs := OriginalAudit.smooth_descent_upper F mu hmu hdiff hlip y (z - y)
  have hyz : y + (z - y) = z := by abel
  rw [hyz] at hs
  dsimp only [lift]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
    norm_sub_sq_real, real_inner_self_eq_norm_sq] at *
  rw [real_inner_comm z y, real_inner_comm (center b c x) y,
    real_inner_comm (center b c x) z] at *
  nlinarith only [hs]

theorem norm_square_affine_hasGradientAt {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    (A : G →L[ℝ] E) (c : E) (z : G) :
    HasGradientAt (fun w : G => ‖A w - c‖ ^ 2)
      ((2 : ℝ) • A.adjoint (A z - c)) z := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hh := ((A.hasFDerivAt (x := z)).sub_const c).norm_sq
  convert! hh using 1
  ext v
  simp only [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, real_inner_smul_left,
    ContinuousLinearMap.adjoint_inner_left, innerSL_apply_apply, two_smul, smul_eq_mul, inner_add_left, ContinuousLinearMap.add_apply]


theorem pullback_hasGradientAt {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    (F : E → ℝ) (hdiff : Differentiable ℝ F) (A : G →L[ℝ] E) (z : G) :
    HasGradientAt (fun w : G => F (A w)) (A.adjoint (gradient F (A z))) z := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hh := ((hdiff (A z)).hasFDerivAt).comp z A.hasFDerivAt
  convert! hh using 1
  ext v
  simp only [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left, inner_gradient_left]

theorem jointLift_hasGradientAt (F : E → ℝ) (hdiff : Differentiable ℝ F)
    (mu b : ℝ) (c : E) (z : JointSliceRegularity.JointSpace E E) :
    HasGradientAt (jointLift F mu b c)
      ((WithLp.sndL 2 ℝ E E).adjoint (gradient F z.snd) -
        (2 * mu) • (affineDifference b).adjoint (affineDifference b z - c)) z := by
  have hh := (pullback_hasGradientAt F hdiff (WithLp.sndL 2 ℝ E E) z).hasFDerivAt.sub
    ((norm_square_affine_hasGradientAt (affineDifference b) c z).hasFDerivAt.const_mul mu)
  rw [hasGradientAt_iff_hasFDerivAt]
  convert! hh using 1
  ext v
  simp only [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, inner_sub_left, real_inner_smul_left,
    ContinuousLinearMap.adjoint_inner_left, inner_sub_right, WithLp.sndL_apply]
  ring

theorem lift_x_hasGradientAt (F : E → ℝ) (mu b : ℝ) (c x y : E) :
    HasGradientAt (fun z => lift F mu b c z y)
      ((2 * mu * b) • (y - center b c x)) x := by
  have hnorm := norm_square_affine_hasGradientAt
    ((-b) • ContinuousLinearMap.id ℝ E) (c - y) x
  have he : (fun z => ‖((-b) • ContinuousLinearMap.id ℝ E) z - (c - y)‖ ^ 2) =
      (fun z => ‖y - center b c z‖ ^ 2) := by
    funext z
    congr 2
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, center]
    module
  rw [he] at hnorm
  have hh := (hasFDerivAt_const (F y) x).sub (hnorm.hasFDerivAt.const_mul mu)
  rw [hasGradientAt_iff_hasFDerivAt]
  convert! hh using 1
  ext v
  simp only [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.adjoint_id,
    ContinuousLinearMap.id_apply, inner_smul_left, inner_sub_left,
    inner_sub_right, real_inner_smul_left, map_smul, smul_smul, center, inner_add_left]
  simp only [starRingEnd_apply, star_trivial]
  ring

theorem lift_y_hasGradientAt (F : E → ℝ) (hdiff : Differentiable ℝ F)
    (mu b : ℝ) (c x y : E) :
    HasGradientAt (lift F mu b c x)
      (gradient F y - (2 * mu) • (y - center b c x)) y := by
  have hnorm := norm_square_affine_hasGradientAt
    (ContinuousLinearMap.id ℝ E) (center b c x) y
  have hh := (hdiff y).hasGradientAt.hasFDerivAt.sub (hnorm.hasFDerivAt.const_mul mu)
  rw [hasGradientAt_iff_hasFDerivAt]
  convert! hh using 1
  ext v
  simp only [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.adjoint_id,
    ContinuousLinearMap.id_apply, inner_sub_left, real_inner_smul_left, smul_smul]
  ring

theorem lift_x_gradient (F : E → ℝ) (mu b : ℝ) (c x y : E) :
    gradient (fun z => lift F mu b c z y) x = (2 * mu * b) • (y - center b c x) :=
  (lift_x_hasGradientAt F mu b c x y).gradient

theorem lift_y_gradient (F : E → ℝ) (hdiff : Differentiable ℝ F)
    (mu b : ℝ) (c x y : E) :
    gradient (lift F mu b c x) y = gradient F y - (2 * mu) • (y - center b c x) :=
  (lift_y_hasGradientAt F hdiff mu b c x y).gradient

theorem lift_differentiable_y (F : E → ℝ) (hdiff : Differentiable ℝ F)
    (mu b : ℝ) (c x : E) : Differentiable ℝ (lift F mu b c x) :=
  fun y => (lift_y_hasGradientAt F hdiff mu b c x y).differentiableAt

theorem lift_differentiable_x (F : E → ℝ) (mu b : ℝ) (c y : E) :
    Differentiable ℝ (fun x => lift F mu b c x y) :=
  fun x => (lift_x_hasGradientAt F mu b c x y).differentiableAt

theorem jointLift_contDiff2 (F : E → ℝ) (hF : ContDiff ℝ 2 F)
    (mu b : ℝ) (c : E) : ContDiff ℝ 2 (jointLift F mu b c) := by
  unfold jointLift
  have hA : ContDiff ℝ 2 (fun z : JointSliceRegularity.JointSpace E E => affineDifference b z - c) :=
    ((affineDifference (E := E) b).contDiff).sub contDiff_const
  exact (hF.comp (WithLp.sndL 2 ℝ E E).contDiff).sub (contDiff_const.mul (ContDiff.norm_sq (𝕜 := ℝ) hA))

theorem gradient_differentiable (F : E → ℝ) (hF : ContDiff ℝ 2 F) :
    Differentiable ℝ (gradient F) := by
  have hder : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have heq : gradient F = fun y => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ F y) := rfl
  rw [heq]
  exact ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp hder).differentiable (by norm_num)

section InnerMaximum
variable [FiniteDimensional ℝ E]

theorem exists_inner_maximum (F : E → ℝ) (mu b : ℝ) (c : E)
    (hmu : 0 < mu) (hdiff : Differentiable ℝ F)
    (hlip : ∀ y z : E, ‖gradient F y - gradient F z‖ ≤ mu * ‖y - z‖)
    (x : E) : ∃ y : E, ∀ z : E, lift F mu b c x z ≤ lift F mu b c x y :=
  OriginalSaddleRegularity.exists_inner_maximum (lift F mu b c) mu hmu
    (negative_y_strongConvex F mu b c hmu hdiff hlip)
    (lift_differentiable_y F hdiff mu b c) x

theorem yStar_maximizes (F : E → ℝ) (mu b : ℝ) (c : E)
    (hmu : 0 < mu) (hdiff : Differentiable ℝ F)
    (hlip : ∀ y z : E, ‖gradient F y - gradient F z‖ ≤ mu * ‖y - z‖)
    (x z : E) : lift F mu b c x z ≤ lift F mu b c x (yStar F mu b c x) :=
  Classical.epsilon_spec (exists_inner_maximum F mu b c hmu hdiff hlip x) z

theorem phi_eq_at_yStar (F : E → ℝ) (mu b : ℝ) (c : E)
    (hmu : 0 < mu) (hdiff : Differentiable ℝ F)
    (hlip : ∀ y z : E, ‖gradient F y - gradient F z‖ ≤ mu * ‖y - z‖)
    (x : E) : phi F mu b c x = lift F mu b c x (yStar F mu b c x) := by
  apply IsGreatest.csSup_eq
  exact ⟨⟨yStar F mu b c x, rfl⟩, by
    rintro _ ⟨z, rfl⟩
    exact yStar_maximizes F mu b c hmu hdiff hlip x z⟩

theorem inner_first_order (F : E → ℝ) (mu b : ℝ) (c : E)
    (hmu : 0 < mu) (hdiff : Differentiable ℝ F)
    (hlip : ∀ y z : E, ‖gradient F y - gradient F z‖ ≤ mu * ‖y - z‖)
    (x : E) : gradient F (yStar F mu b c x) =
      (2 * mu) • (yStar F mu b c x - center b c x) := by
  have hmin : ∀ z : E, -lift F mu b c x (yStar F mu b c x) ≤ -lift F mu b c x z :=
    fun z => neg_le_neg (yStar_maximizes F mu b c hmu hdiff hlip x z)
  have hz := PacketCore.gradient_eq_zero_at_global_min
    (fun y => -lift F mu b c x y) (yStar F mu b c x) hmin
  rw [OriginalSaddleRegularity.gradient_neg_of_differentiable _
    (lift_differentiable_y F hdiff mu b c x), lift_y_gradient F hdiff mu b c] at hz
  exact sub_eq_zero.mp (neg_eq_zero.mp hz)

theorem inner_maximum_unique (F : E → ℝ) (mu b : ℝ) (c : E)
    (hmu : 0 < mu) (hdiff : Differentiable ℝ F)
    (hlip : ∀ y z : E, ‖gradient F y - gradient F z‖ ≤ mu * ‖y - z‖)
    (x y : E) (hy : ∀ z : E, lift F mu b c x z ≤ lift F mu b c x y) :
    yStar F mu b c x = y := by
  have hg := OriginalSaddleRegularity.inner_maximum_quadratic_gap (lift F mu b c) mu
    (negative_y_strongConvex F mu b c hmu hdiff hlip)
    (lift_differentiable_y F hdiff mu b c) (yStar F mu b c)
    (yStar_maximizes F mu b c hmu hdiff hlip) x y
  have hm := hy (yStar F mu b c x)
  have hn : ‖y - yStar F mu b c x‖ ^ 2 ≤ 0 := by nlinarith only [hg, hm, hmu]
  have hnzero : y - yStar F mu b c x = 0 := by
    exact norm_eq_zero.mp (by nlinarith only [hn, norm_nonneg (y - yStar F mu b c x)])
  exact (sub_eq_zero.mp hnzero).symm

theorem stationary_is_inner_maximum (F : E → ℝ) (mu b : ℝ) (c : E)
    (hmu : 0 < mu) (hdiff : Differentiable ℝ F)
    (hlip : ∀ y z : E, ‖gradient F y - gradient F z‖ ≤ mu * ‖y - z‖)
    (x y : E) (hy : gradient F y = (2 * mu) • (y - center b c x)) :
    ∀ z : E, lift F mu b c x z ≤ lift F mu b c x y := by
  have hzero : gradient (fun z => -lift F mu b c x z) y = 0 := by
    rw [OriginalSaddleRegularity.gradient_neg_of_differentiable _
      (lift_differentiable_y F hdiff mu b c x), lift_y_gradient F hdiff mu b c, hy]
    simp
  intro z
  have hs := PacketCore.strongConvex_support (fun y => -lift F mu b c x y) mu
    (negative_y_strongConvex F mu b c hmu hdiff hlip x)
    (lift_differentiable_y F hdiff mu b c x).neg y z
  rw [hzero, inner_zero_left, add_zero] at hs
  have hnonneg : 0 ≤ mu / 2 * ‖z - y‖ ^ 2 := by positivity
  linarith only [hs, hnonneg]

noncomputable def initialShift (F : E → ℝ) (mu : ℝ) : E :=
  -((2 * mu)⁻¹ • gradient F 0)

theorem initial_inner_exact (F : E → ℝ) (mu b : ℝ)
    (hmu : 0 < mu) (hdiff : Differentiable ℝ F)
    (hlip : ∀ y z : E, ‖gradient F y - gradient F z‖ ≤ mu * ‖y - z‖) :
    yStar F mu b (initialShift F mu) 0 = 0 := by
  apply inner_maximum_unique F mu b (initialShift F mu) hmu hdiff hlip 0 0
  apply stationary_is_inner_maximum F mu b (initialShift F mu) hmu hdiff hlip 0 0
  simp only [center, smul_zero, zero_add, initialShift, sub_neg_eq_add, zero_add,
    smul_smul, mul_inv_cancel₀ (by positivity : 2 * mu ≠ 0), one_smul]

theorem x_slice_lipschitz (F : E → ℝ) (mu b : ℝ) (c : E) (hmu : 0 < mu) :
    (∀ y x z : E, ‖gradient (fun t => lift F mu b c t y) x -
      gradient (fun t => lift F mu b c t y) z‖ ≤
      (2 * mu * (1 + b ^ 2 + |b|)) * ‖x - z‖) ∧
    (∀ x y z : E, ‖gradient (fun t => lift F mu b c t y) x -
      gradient (fun t => lift F mu b c t z) x‖ ≤
      (2 * mu * (1 + b ^ 2 + |b|)) * ‖y - z‖) := by
  constructor
  · intro y x z
    rw [lift_x_gradient, lift_x_gradient]
    have he : (2 * mu * b) • (y - center b c x) -
        (2 * mu * b) • (y - center b c z) = (-2 * mu * b ^ 2) • (x - z) := by
      dsimp only [center]
      module
    rw [he, norm_smul, Real.norm_eq_abs]
    have ha : |(-2 * mu * b ^ 2)| = 2 * mu * b ^ 2 := by
      rw [abs_of_nonpos (by nlinarith only [sq_nonneg b, hmu])]
      ring
    rw [ha]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have hn := abs_nonneg b
    nlinarith only [hmu, hn]
  · intro x y z
    rw [lift_x_gradient, lift_x_gradient, ← smul_sub]
    have he : (y - center b c x) - (z - center b c x) = y - z := by abel
    rw [he, norm_smul, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hmu]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    nlinarith only [hmu, sq_nonneg b]

theorem phi_hasGradientAt (F : E → ℝ) (mu b : ℝ) (c : E)
    (hmu : 0 < mu) (hdiff : Differentiable ℝ F)
    (hlip : ∀ y z : E, ‖gradient F y - gradient F z‖ ≤ mu * ‖y - z‖)
    (x : E) : HasGradientAt (phi F mu b c) (b • gradient F (yStar F mu b c x)) x := by
  have heq : phi F mu b c = OriginalSaddleRegularity.value (lift F mu b c) (yStar F mu b c) := by
    funext z
    exact phi_eq_at_yStar F mu b c hmu hdiff hlip z
  have hs := x_slice_lipschitz F mu b c hmu
  have hL : 0 < 2 * mu * (1 + b ^ 2 + |b|) := by positivity
  have hh := OriginalSaddleRegularity.value_hasGradientAt (lift F mu b c)
    (2 * mu * (1 + b ^ 2 + |b|)) mu hL hmu
    (fun y => lift_differentiable_x F mu b c y)
    (lift_differentiable_y F hdiff mu b c)
    (negative_y_strongConvex F mu b c hmu hdiff hlip)
    hs.1 hs.2 (yStar F mu b c) (yStar_maximizes F mu b c hmu hdiff hlip) x
  rw [← heq, lift_x_gradient] at hh
  have hFOC := inner_first_order F mu b c hmu hdiff hlip x
  rw [hFOC]
  convert! hh using 1 <;> module

end InnerMaximum
end AllDerivativeLift

namespace AllDerivativeLift
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def preimage (F : E → ℝ) (mu b : ℝ) (c y : E) : E :=
  b⁻¹ • (y - c - (2 * mu)⁻¹ • gradient F y)

theorem center_preimage (F : E → ℝ) (mu b : ℝ) (c y : E) (hb : b ≠ 0) :
    center b c (preimage F mu b c y) = y - (2 * mu)⁻¹ • gradient F y := by
  simp only [center, preimage, smul_smul, mul_inv_cancel₀ hb, one_smul]
  abel

theorem preimage_inner_exact (F : E → ℝ) (mu b : ℝ) (c y : E)
    (hmu : 0 < mu) (hb : b ≠ 0) (hdiff : Differentiable ℝ F)
    (hlip : ∀ y z : E, ‖gradient F y - gradient F z‖ ≤ mu * ‖y - z‖) :
    yStar F mu b c (preimage F mu b c y) = y := by
  apply inner_maximum_unique F mu b c hmu hdiff hlip
  apply stationary_is_inner_maximum F mu b c hmu hdiff hlip
  rw [center_preimage F mu b c y hb]
  have he : y - (y - (2 * mu)⁻¹ • gradient F y) = (2 * mu)⁻¹ • gradient F y := by abel
  rw [he, smul_smul, mul_inv_cancel₀ (by positivity : 2 * mu ≠ 0), one_smul]

theorem phi_preimage_value (F : E → ℝ) (mu b : ℝ) (c y : E)
    (hmu : 0 < mu) (hb : b ≠ 0) (hdiff : Differentiable ℝ F)
    (hlip : ∀ y z : E, ‖gradient F y - gradient F z‖ ≤ mu * ‖y - z‖) :
    phi F mu b c (preimage F mu b c y) = F y - ‖gradient F y‖ ^ 2 / (4 * mu) := by
  rw [phi_eq_at_yStar F mu b c hmu hdiff hlip, preimage_inner_exact F mu b c y hmu hb hdiff hlip]
  unfold lift
  rw [center_preimage F mu b c y hb]
  have he : y - (y - (2 * mu)⁻¹ • gradient F y) = (2 * mu)⁻¹ • gradient F y := by abel
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by positivity : 0 < 2 * mu))]
  field_simp
  <;> ring

theorem phi_infimum_eq (F : E → ℝ) (mu b : ℝ) (c : E)
    (hmu : 0 < mu) (hb : b ≠ 0) (hdiff : Differentiable ℝ F)
    (hlip : ∀ y z : E, ‖gradient F y - gradient F z‖ ≤ mu * ‖y - z‖) :
    sInf (Set.range (phi F mu b c)) = sInf (Set.range F) := by
  apply csInf_eq_csInf_of_forall_exists_le
  · rintro _ ⟨x, rfl⟩
    refine ⟨F (center b c x), ⟨center b c x, rfl⟩, ?_⟩
    rw [phi_eq_at_yStar F mu b c hmu hdiff hlip]
    have hh := yStar_maximizes F mu b c hmu hdiff hlip x (center b c x)
    simpa only [lift, sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, sub_zero] using hh
  · rintro _ ⟨y, rfl⟩
    refine ⟨phi F mu b c (preimage F mu b c y), ⟨preimage F mu b c y, rfl⟩, ?_⟩
    rw [phi_preimage_value F mu b c y hmu hb hdiff hlip]
    have hn : 0 ≤ ‖gradient F y‖ ^ 2 / (4 * mu) := by positivity
    linarith only [hn]

theorem lift_initial_gap (F : E → ℝ) (mu b Delta : ℝ)
    (hmu : 0 < mu) (hb : b ≠ 0) (hdiff : Differentiable ℝ F)
    (hlip : ∀ y z : E, ‖gradient F y - gradient F z‖ ≤ mu * ‖y - z‖)
    (hgap : F 0 - sInf (Set.range F) ≤ Delta) :
    phi F mu b (initialShift F mu) 0 -
      sInf (Set.range (phi F mu b (initialShift F mu))) ≤ Delta := by
  rw [phi_infimum_eq F mu b (initialShift F mu) hmu hb hdiff hlip,
    phi_eq_at_yStar F mu b (initialShift F mu) hmu hdiff hlip,
    initial_inner_exact F mu b hmu hdiff hlip]
  unfold lift
  have hn : 0 ≤ mu * ‖(0 : E) - center b (initialShift F mu) 0‖ ^ 2 := by positivity
  linarith only [hgap, hn]

theorem lift_stationarity_absolute (F : E → ℝ) (mu b : ℝ) (c : E)
    (hmu : 0 < mu) (hb : b ≠ 0) (hdiff : Differentiable ℝ F)
    (hlip : ∀ y z : E, ‖gradient F y - gradient F z‖ ≤ mu * ‖y - z‖) (x : E) :
    ‖gradient F (center b c x)‖ ≤ (3 / (2 * |b|)) * ‖gradient (phi F mu b c) x‖ := by
  let y := yStar F mu b c x
  have hfoc := inner_first_order F mu b c hmu hdiff hlip x
  have hres : y - center b c x = (2 * mu)⁻¹ • gradient F y := by
    rw [hfoc, smul_smul, inv_mul_cancel₀ (by positivity : 2 * mu ≠ 0), one_smul]
  have hdist : ‖center b c x - y‖ = ‖gradient F y‖ / (2 * mu) := by
    rw [norm_sub_rev, hres, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (by positivity : 0 < 2 * mu))]
    ring
  have ht : ‖gradient F (center b c x)‖ ≤
      ‖gradient F (center b c x) - gradient F y‖ + ‖gradient F y‖ := norm_le_norm_sub_add _ _
  have hl := hlip (center b c x) y
  rw [hdist] at hl
  have hhalf : mu * (‖gradient F y‖ / (2 * mu)) = ‖gradient F y‖ / 2 := by field_simp
  rw [hhalf] at hl
  have hg : gradient (phi F mu b c) x = b • gradient F y :=
    (phi_hasGradientAt F mu b c hmu hdiff hlip x).gradient
  rw [hg, norm_smul, Real.norm_eq_abs]
  have hc : (3 / (2 * |b|)) * (|b| * ‖gradient F y‖) = (3 / 2) * ‖gradient F y‖ := by
    field_simp [abs_ne_zero.mpr hb]
  rw [hc]
  linarith only [ht, hl]

theorem lift_stationarity_positive (F : E → ℝ) (mu b : ℝ) (c : E)
    (hmu : 0 < mu) (hb : 0 < b) (hdiff : Differentiable ℝ F)
    (hlip : ∀ y z : E, ‖gradient F y - gradient F z‖ ≤ mu * ‖y - z‖) (x : E) :
    ‖gradient F (center b c x)‖ ≤ (3 / (2 * b)) * ‖gradient (phi F mu b c) x‖ := by
  simpa only [abs_of_pos hb] using lift_stationarity_absolute F mu b c hmu (ne_of_gt hb) hdiff hlip x

end AllDerivativeLift

namespace AllDerivativeLift
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def quadraticHessian (b : ℝ) :
    JointSliceRegularity.JointSpace E E →L[ℝ] JointSliceRegularity.JointSpace E E :=
  (affineDifference b).adjoint.comp (affineDifference b)

theorem projection_norm_le_one : ‖WithLp.sndL 2 ℝ E E‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simpa only [one_mul, WithLp.sndL_apply] using JointSliceRegularity.norm_snd_projection z

theorem projection_adjoint_contraction (v : E) :
    ‖(WithLp.sndL 2 ℝ E E).adjoint v‖ ≤ ‖v‖ := by
  have hn : ‖(WithLp.sndL 2 ℝ E E).adjoint‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact projection_norm_le_one
  have hh := mul_le_mul_of_nonneg_right hn (norm_nonneg v)
  exact le_trans (ContinuousLinearMap.le_opNorm _ _) (by simpa only [one_mul] using hh)

theorem affineDifference_norm_bound (b : ℝ) (z : JointSliceRegularity.JointSpace E E) :
    ‖affineDifference b z‖ ≤ Real.sqrt (1 + b ^ 2) * ‖z‖ := by
  have ht : ‖affineDifference b z‖ ≤ ‖z.snd‖ + |b| * ‖z.fst‖ := by
    simpa only [affineDifference, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, WithLp.sndL_apply, WithLp.fstL_apply,
      norm_smul, Real.norm_eq_abs] using norm_sub_le z.snd (b • z.fst)
  have htsq := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ ‖z.snd‖ + |b| * ‖z.fst‖)).mpr ht
  have hcs := sq_nonneg (‖z.fst‖ - |b| * ‖z.snd‖)
  have habs := sq_abs b
  have hz := WithLp.prod_norm_sq_eq_of_L2 z
  have hroot := Real.sq_sqrt (by positivity : 0 ≤ 1 + b ^ 2)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ Real.sqrt (1 + b ^ 2) * ‖z‖)).mp
  nlinarith only [htsq, hcs, habs, hz, hroot]

theorem quadraticHessian_norm_bound (b : ℝ) :
    ‖quadraticHessian (E := E) b‖ ≤ 1 + b ^ 2 := by
  have hA : ‖affineDifference (E := E) b‖ ≤ Real.sqrt (1 + b ^ 2) := by
    exact ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) (affineDifference_norm_bound b)
  unfold quadraticHessian
  rw [ContinuousLinearMap.norm_adjoint_comp_self]
  have hs := (sq_le_sq₀ (norm_nonneg (affineDifference (E := E) b)) (Real.sqrt_nonneg (1 + b ^ 2))).mpr hA
  rw [Real.sq_sqrt (by positivity : 0 ≤ 1 + b ^ 2)] at hs
  nlinarith only [hs]

theorem jointLift_gradient (F : E → ℝ) (hdiff : Differentiable ℝ F)
    (mu b : ℝ) (c : E) (z : JointSliceRegularity.JointSpace E E) :
    gradient (jointLift F mu b c) z =
      (WithLp.sndL 2 ℝ E E).adjoint (gradient F z.snd) -
        (2 * mu) • (affineDifference b).adjoint (affineDifference b z - c) :=
  (jointLift_hasGradientAt F hdiff mu b c z).gradient

theorem jointLift_gradient_difference (F : E → ℝ) (hdiff : Differentiable ℝ F)
    (mu b : ℝ) (c : E) (z w : JointSliceRegularity.JointSpace E E) :
    gradient (jointLift F mu b c) z - gradient (jointLift F mu b c) w =
      (WithLp.sndL 2 ℝ E E).adjoint (gradient F z.snd - gradient F w.snd) -
        (2 * mu) • quadraticHessian b (z - w) := by
  rw [jointLift_gradient F hdiff, jointLift_gradient F hdiff]
  simp only [quadraticHessian, ContinuousLinearMap.comp_apply, map_sub, smul_sub]
  abel

theorem jointLift_gradient_lipschitz (F : E → ℝ) (mu b : ℝ) (c : E)
    (hmu : 0 < mu) (hdiff : Differentiable ℝ F)
    (hlip : ∀ y z : E, ‖gradient F y - gradient F z‖ ≤ mu * ‖y - z‖)
    (z w : JointSliceRegularity.JointSpace E E) :
    ‖gradient (jointLift F mu b c) z - gradient (jointLift F mu b c) w‖ ≤
      (mu * (3 + 2 * b ^ 2)) * ‖z - w‖ := by
  rw [jointLift_gradient_difference F hdiff]
  have hfirst : ‖(WithLp.sndL 2 ℝ E E).adjoint (gradient F z.snd - gradient F w.snd)‖ ≤
      mu * ‖z - w‖ := by
    exact le_trans (projection_adjoint_contraction _)
      (le_trans (hlip z.snd w.snd)
        (mul_le_mul_of_nonneg_left (JointSliceRegularity.norm_snd_projection_sub z w) hmu.le))
  have hlast : ‖(2 * mu) • quadraticHessian b (z - w)‖ ≤
      (2 * mu) * (1 + b ^ 2) * ‖z - w‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * mu)]
    have hQ : ‖quadraticHessian (E := E) b (z - w)‖ ≤ (1 + b ^ 2) * ‖z - w‖ :=
      le_trans (ContinuousLinearMap.le_opNorm (quadraticHessian (E := E) b) (z - w))
        (mul_le_mul_of_nonneg_right (quadraticHessian_norm_bound (E := E) b) (norm_nonneg (z - w)))
    calc
      (2 * mu) * ‖quadraticHessian b (z - w)‖
        ≤ (2 * mu) * ((1 + b ^ 2) * ‖z - w‖) := mul_le_mul_of_nonneg_left hQ (by positivity)
      _ = (2 * mu) * (1 + b ^ 2) * ‖z - w‖ := by ring
  have ht := norm_sub_le ((WithLp.sndL 2 ℝ E E).adjoint (gradient F z.snd - gradient F w.snd))
    ((2 * mu) • quadraticHessian b (z - w))
  nlinarith only [ht, hfirst, hlast]

theorem jointLift_gradient_hasFDerivAt (F : E → ℝ) (hF : ContDiff ℝ 2 F)
    (mu b : ℝ) (c : E) (z : JointSliceRegularity.JointSpace E E) :
    HasFDerivAt (gradient (jointLift F mu b c))
      (((WithLp.sndL 2 ℝ E E).adjoint.comp (fderiv ℝ (gradient F) z.snd)).comp
        (WithLp.sndL 2 ℝ E E) - (2 * mu) • quadraticHessian b) z := by
  have hgF := gradient_differentiable F hF
  have hgrad : gradient (jointLift F mu b c) = fun w =>
      (WithLp.sndL 2 ℝ E E).adjoint (gradient F w.snd) -
        (2 * mu) • (affineDifference b).adjoint (affineDifference b w - c) := by
    funext w
    exact jointLift_gradient F (hF.differentiable (by norm_num)) mu b c w
  rw [hgrad]
  have hfirst := ((WithLp.sndL 2 ℝ E E).adjoint.hasFDerivAt).comp z
    ((hgF z.snd).hasFDerivAt.comp z (WithLp.sndL 2 ℝ E E).hasFDerivAt)
  have hlast := (((affineDifference b).adjoint.hasFDerivAt).comp z
    (((affineDifference b).hasFDerivAt).sub_const c)).const_smul (2 * mu)
  convert! hfirst.sub hlast using 1

theorem jointLift_hessian_formula (F : E → ℝ) (hF : ContDiff ℝ 2 F)
    (mu b : ℝ) (c : E) (z : JointSliceRegularity.JointSpace E E) :
    fderiv ℝ (gradient (jointLift F mu b c)) z =
      ((WithLp.sndL 2 ℝ E E).adjoint.comp (fderiv ℝ (gradient F) z.snd)).comp
        (WithLp.sndL 2 ℝ E E) - (2 * mu) • quadraticHessian b :=
  (jointLift_gradient_hasFDerivAt F hF mu b c z).fderiv

end AllDerivativeLift

namespace AllDerivativeLift
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem hessian_sandwich_norm_le (H : E →L[ℝ] E) :
    ‖((WithLp.sndL 2 ℝ E E).adjoint.comp H).comp (WithLp.sndL 2 ℝ E E)‖ ≤ ‖H‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg H)
  intro v
  simp only [ContinuousLinearMap.comp_apply]
  exact le_trans (projection_adjoint_contraction _)
    (le_trans (ContinuousLinearMap.le_opNorm H _)
      (mul_le_mul_of_nonneg_left (JointSliceRegularity.norm_snd_projection v) (norm_nonneg H)))

theorem jointLift_hessian_difference (F : E → ℝ) (hF : ContDiff ℝ 2 F)
    (mu b : ℝ) (c : E) (z w : JointSliceRegularity.JointSpace E E) :
    fderiv ℝ (gradient (jointLift F mu b c)) z - fderiv ℝ (gradient (jointLift F mu b c)) w =
      ((WithLp.sndL 2 ℝ E E).adjoint.comp
        (fderiv ℝ (gradient F) z.snd - fderiv ℝ (gradient F) w.snd)).comp (WithLp.sndL 2 ℝ E E) := by
  rw [jointLift_hessian_formula F hF, jointLift_hessian_formula F hF]
  ext v
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, map_sub]
  abel

theorem jointLift_hessian_lipschitz (F : E → ℝ) (hF : ContDiff ℝ 2 F)
    (mu b rho : ℝ) (c : E) (hrho : 0 ≤ rho)
    (hH : ∀ y v : E, ‖fderiv ℝ (gradient F) y - fderiv ℝ (gradient F) v‖ ≤ rho * ‖y - v‖)
    (z w : JointSliceRegularity.JointSpace E E) :
    ‖fderiv ℝ (gradient (jointLift F mu b c)) z - fderiv ℝ (gradient (jointLift F mu b c)) w‖ ≤
      rho * ‖z - w‖ := by
  rw [jointLift_hessian_difference F hF]
  exact le_trans (hessian_sandwich_norm_le _)
    (le_trans (hH z.snd w.snd)
      (mul_le_mul_of_nonneg_left (JointSliceRegularity.norm_snd_projection_sub z w) hrho))

theorem jointLift_hessian_norm (F : E → ℝ) (mu b : ℝ) (c : E)
    (hmu : 0 < mu) (hdiff : Differentiable ℝ F)
    (hlip : ∀ y z : E, ‖gradient F y - gradient F z‖ ≤ mu * ‖y - z‖)
    (z : JointSliceRegularity.JointSpace E E) :
    ‖fderiv ℝ (gradient (jointLift F mu b c)) z‖ ≤ mu * (3 + 2 * b ^ 2) := by
  let C : NNReal := ⟨mu * (3 + 2 * b ^ 2), by positivity⟩
  have hLip : LipschitzWith C (gradient (jointLift F mu b c)) :=
    lipschitzWith_iff_norm_sub_le.mpr (jointLift_gradient_lipschitz F mu b c hmu hdiff hlip)
  exact norm_fderiv_le_of_lipschitz ℝ hLip

noncomputable def simulateBundle (mu b : ℝ) (c : E) (z : JointSliceRegularity.JointSpace E E)
    (Fy : ℝ) (gy : E) (Hy : E →L[ℝ] E) :
    ℝ × JointSliceRegularity.JointSpace E E ×
      (JointSliceRegularity.JointSpace E E →L[ℝ] JointSliceRegularity.JointSpace E E) :=
  (Fy - mu * ‖affineDifference b z - c‖ ^ 2,
    (WithLp.sndL 2 ℝ E E).adjoint gy - (2 * mu) • (affineDifference b).adjoint (affineDifference b z - c),
    ((WithLp.sndL 2 ℝ E E).adjoint.comp Hy).comp (WithLp.sndL 2 ℝ E E) - (2 * mu) • quadraticHessian b)

noncomputable def actualBundle (F : E → ℝ) (mu b : ℝ) (c : E)
    (z : JointSliceRegularity.JointSpace E E) :
    ℝ × JointSliceRegularity.JointSpace E E ×
      (JointSliceRegularity.JointSpace E E →L[ℝ] JointSliceRegularity.JointSpace E E) :=
  (jointLift F mu b c z, gradient (jointLift F mu b c) z,
    fderiv ℝ (gradient (jointLift F mu b c)) z)

theorem one_query_bundle_simulation (F : E → ℝ) (hF : ContDiff ℝ 2 F)
    (mu b : ℝ) (c : E) (z : JointSliceRegularity.JointSpace E E) :
    simulateBundle mu b c z (F z.snd) (gradient F z.snd) (fderiv ℝ (gradient F) z.snd) =
      actualBundle F mu b c z := by
  simp only [simulateBundle, actualBundle, jointLift,
    jointLift_gradient F (hF.differentiable (by norm_num)), jointLift_hessian_formula F hF]

noncomputable def scaleB (kappa : ℝ) : ℝ := Real.sqrt ((kappa - 3) / 2)

theorem scaleB_properties (kappa : ℝ) (hk : 6 ≤ kappa) :
    0 < scaleB kappa ∧ (scaleB kappa) ^ 2 = (kappa - 3) / 2 ∧
    3 / 2 ≤ (scaleB kappa) ^ 2 ∧ 3 + 2 * (scaleB kappa) ^ 2 = kappa := by
  have hpos : 0 < (kappa - 3) / 2 := by linarith only [hk]
  have hs : (scaleB kappa) ^ 2 = (kappa - 3) / 2 := Real.sq_sqrt hpos.le
  refine ⟨Real.sqrt_pos.mpr hpos, hs, ?_, ?_⟩ <;> linarith only [hs, hk]

end AllDerivativeLift

namespace AllDerivativeLift
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem lift_validity_stationarity_all_items
    (F : E → ℝ) (mu kappa rho Delta : ℝ)
    (hmu : 0 < mu) (hk : 6 ≤ kappa) (hrho : 0 < rho)
    (hF : ContDiff ℝ 2 F)
    (hlip : ∀ y z : E, ‖gradient F y - gradient F z‖ ≤ mu * ‖y - z‖)
    (hH : ∀ y z : E, ‖fderiv ℝ (gradient F) y - fderiv ℝ (gradient F) z‖ ≤ rho * ‖y - z‖)
    (hgap : F 0 - sInf (Set.range F) ≤ Delta) :
    let b := scaleB kappa
    let c := initialShift F mu
    let L := mu * kappa
    ContDiff ℝ 2 (jointLift F mu b c) ∧
    (∀ x : E, StrongConcaveOn (Set.univ : Set E) mu (lift F mu b c x)) ∧
    (∀ z w : JointSliceRegularity.JointSpace E E,
      ‖gradient (jointLift F mu b c) z - gradient (jointLift F mu b c) w‖ ≤ L * ‖z - w‖) ∧
    (∀ z : JointSliceRegularity.JointSpace E E,
      ‖fderiv ℝ (gradient (jointLift F mu b c)) z‖ ≤ L) ∧
    (∀ z w : JointSliceRegularity.JointSpace E E,
      ‖fderiv ℝ (gradient (jointLift F mu b c)) z - fderiv ℝ (gradient (jointLift F mu b c)) w‖ ≤
        rho * ‖z - w‖) ∧
    (∀ x : E, ∃! y : E, ∀ z : E, lift F mu b c x z ≤ lift F mu b c x y) ∧
    yStar F mu b c 0 = 0 ∧
    Differentiable ℝ (phi F mu b c) ∧
    sInf (Set.range (phi F mu b c)) = sInf (Set.range F) ∧
    phi F mu b c 0 - sInf (Set.range (phi F mu b c)) ≤ Delta ∧
    (∀ x : E, ‖gradient F (center b c x)‖ ≤
      (3 / (2 * b)) * ‖gradient (phi F mu b c) x‖) ∧
    (∀ z : JointSliceRegularity.JointSpace E E,
      simulateBundle mu b c z (F z.snd) (gradient F z.snd) (fderiv ℝ (gradient F) z.snd) =
        actualBundle F mu b c z) := by
  dsimp only
  have hdiff := hF.differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hb := scaleB_properties kappa hk
  have hL : mu * (3 + 2 * (scaleB kappa) ^ 2) = mu * kappa := by rw [hb.2.2.2]
  refine ⟨jointLift_contDiff2 F hF mu (scaleB kappa) (initialShift F mu), ?_, ?_, ?_, ?_, ?_,
    initial_inner_exact F mu (scaleB kappa) hmu hdiff hlip, ?_,
    phi_infimum_eq F mu (scaleB kappa) (initialShift F mu) hmu (ne_of_gt hb.1) hdiff hlip,
    lift_initial_gap F mu (scaleB kappa) Delta hmu (ne_of_gt hb.1) hdiff hlip hgap,
    lift_stationarity_positive F mu (scaleB kappa) (initialShift F mu) hmu hb.1 hdiff hlip,
    one_query_bundle_simulation F hF mu (scaleB kappa) (initialShift F mu)⟩
  · intro x
    have hc := UniformConvexOn.neg
      (negative_y_strongConvex F mu (scaleB kappa) (initialShift F mu) hmu hdiff hlip x)
    have he : (-(fun y : E => -lift F mu (scaleB kappa) (initialShift F mu) x y)) =
        lift F mu (scaleB kappa) (initialShift F mu) x := by
      funext y
      simp only [Pi.neg_apply, neg_neg]
    rw [he] at hc
    exact hc
  · intro z w
    simpa only [hL] using
      jointLift_gradient_lipschitz F mu (scaleB kappa) (initialShift F mu) hmu hdiff hlip z w
  · intro z
    simpa only [hL] using jointLift_hessian_norm F mu (scaleB kappa) (initialShift F mu) hmu hdiff hlip z
  · exact jointLift_hessian_lipschitz F hF mu (scaleB kappa) rho (initialShift F mu) hrho.le hH
  · intro x
    refine ⟨yStar F mu (scaleB kappa) (initialShift F mu) x,
      yStar_maximizes F mu (scaleB kappa) (initialShift F mu) hmu hdiff hlip x, ?_⟩
    intro y hy
    exact (inner_maximum_unique F mu (scaleB kappa) (initialShift F mu) hmu hdiff hlip x y hy).symm
  · intro x
    exact (phi_hasGradientAt F mu (scaleB kappa) (initialShift F mu) hmu hdiff hlip x).differentiableAt

end AllDerivativeLift

namespace AllDerivativeLift
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem gradient_lipschitz_from_hessian_norm (F : E → ℝ) (hF : ContDiff ℝ 2 F)
    (mu : ℝ) (hFnorm : ∀ y : E, ‖fderiv ℝ (gradient F) y‖ ≤ mu) :
    ∀ y z : E, ‖gradient F y - gradient F z‖ ≤ mu * ‖y - z‖ := by
  intro y z
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => gradient_differentiable F hF x) (fun x _ => hFnorm x)
    convex_univ (Set.mem_univ z) (Set.mem_univ y)

theorem lift_from_F_class
    (F : E → ℝ) (mu kappa rho Delta : ℝ)
    (hmu : 0 < mu) (hk : 6 ≤ kappa) (hrho : 0 < rho)
    (hF : ContDiff ℝ 2 F)
    (hFnorm : ∀ y : E, ‖fderiv ℝ (gradient F) y‖ ≤ mu)
    (hH : ∀ y z : E, ‖fderiv ℝ (gradient F) y - fderiv ℝ (gradient F) z‖ ≤ rho * ‖y - z‖)
    (hgap : F 0 - sInf (Set.range F) ≤ Delta) :
    let b := scaleB kappa
    let c := initialShift F mu
    let L := mu * kappa
    ContDiff ℝ 2 (jointLift F mu b c) ∧
    (∀ x : E, StrongConcaveOn (Set.univ : Set E) mu (lift F mu b c x)) ∧
    (∀ z w : JointSliceRegularity.JointSpace E E,
      ‖gradient (jointLift F mu b c) z - gradient (jointLift F mu b c) w‖ ≤ L * ‖z - w‖) ∧
    (∀ z : JointSliceRegularity.JointSpace E E,
      ‖fderiv ℝ (gradient (jointLift F mu b c)) z‖ ≤ L) ∧
    (∀ z w : JointSliceRegularity.JointSpace E E,
      ‖fderiv ℝ (gradient (jointLift F mu b c)) z - fderiv ℝ (gradient (jointLift F mu b c)) w‖ ≤
        rho * ‖z - w‖) ∧
    (∀ x : E, ∃! y : E, ∀ z : E, lift F mu b c x z ≤ lift F mu b c x y) ∧
    yStar F mu b c 0 = 0 ∧
    Differentiable ℝ (phi F mu b c) ∧
    sInf (Set.range (phi F mu b c)) = sInf (Set.range F) ∧
    phi F mu b c 0 - sInf (Set.range (phi F mu b c)) ≤ Delta ∧
    (∀ x : E, ‖gradient F (center b c x)‖ ≤
      (3 / (2 * b)) * ‖gradient (phi F mu b c) x‖) ∧
    (∀ z : JointSliceRegularity.JointSpace E E,
      simulateBundle mu b c z (F z.snd) (gradient F z.snd) (fderiv ℝ (gradient F) z.snd) =
        actualBundle F mu b c z) := by
  exact lift_validity_stationarity_all_items F mu kappa rho Delta hmu hk hrho hF
    (gradient_lipschitz_from_hessian_norm F hF mu hFnorm) hH hgap

end AllDerivativeLift
end

section
-- Source component: LiftOracleJetBridge.lean

open scoped ContDiff

namespace FangqingLiftOracleJetBridge

open FangqingSingleLowerAllDerivativeOracle AllDerivativeLift

noncomputable section
set_option maxHeartbeats 5000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

abbrev Joint (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :=
  JointSliceRegularity.JointSpace E E
abbrev SaddleResponse (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :=
  ℝ × Joint E × (Joint E →L[ℝ] Joint E)

def jetValue (r : AllDerivativeResponse E) : ℝ :=
  continuousMultilinearCurryFin0 ℝ E ℝ (r 0)
def jetGradient (r : AllDerivativeResponse E) : E :=
  (InnerProductSpace.toDual ℝ E).symm (continuousMultilinearCurryFin1 ℝ E ℝ (r 1))
def jetSecond (r : AllDerivativeResponse E) : E →L[ℝ] E →L[ℝ] ℝ :=
  continuousMultilinearCurryFin1 ℝ E (E →L[ℝ] ℝ)
    (continuousMultilinearCurryRightEquiv' ℝ 1 E ℝ (r 2))
def jetHessian (r : AllDerivativeResponse E) : E →L[ℝ] E :=
  (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp (jetSecond r)

theorem curry_one_actual_derivative {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (F : E → G) (y : E) :
    continuousMultilinearCurryFin1 ℝ E G (iteratedFDeriv ℝ 1 F y) = fderiv ℝ F y := by
  ext v
  rw [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
  rfl

theorem jet_value_actual (F : E → ℝ) (y : E) : jetValue (allDerivativeOracle F y) = F y := by
  simp [jetValue, allDerivativeOracle, continuousMultilinearCurryFin0_apply]

theorem jet_gradient_actual (F : E → ℝ) (y : E) :
    jetGradient (allDerivativeOracle F y) = gradient F y := by
  rw [jetGradient, allDerivativeOracle, curry_one_actual_derivative]
  rfl

theorem jet_second_actual (F : E → ℝ) (y : E) :
    jetSecond (allDerivativeOracle F y) = fderiv ℝ (fderiv ℝ F) y := by
  have hh := congrArg (continuousMultilinearCurryRightEquiv' ℝ 1 E ℝ)
    (iteratedFDeriv_succ_eq_comp_right (f := F) (x := y) (n := 1))
  simp only [Function.comp_apply, LinearIsometryEquiv.apply_symm_apply] at hh
  change continuousMultilinearCurryFin1 ℝ E (E →L[ℝ] ℝ)
    (continuousMultilinearCurryRightEquiv' ℝ 1 E ℝ (iteratedFDeriv ℝ 2 F y)) = _
  rw [hh, curry_one_actual_derivative]

theorem jet_hessian_actual (F : E → ℝ) (hF : ContDiff ℝ 2 F) (y : E) :
    jetHessian (allDerivativeOracle F y) = fderiv ℝ (gradient F) y := by
  rw [jetHessian, jet_second_actual]
  have hdf : DifferentiableAt ℝ (fderiv ℝ F) y :=
    ((hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) y
  have hh := ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp y hdf.hasFDerivAt).fderiv
  have heq : gradient F = fun x =>
      (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap (fderiv ℝ F x) := by
    funext x
    rfl
  rw [heq]
  exact hh.symm

theorem gradient_hessian_is_actual_riesz_image (F : E → ℝ) (hF : ContDiff ℝ 2 F) (y : E) :
    fderiv ℝ (gradient F) y =
      (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (fderiv ℝ (fderiv ℝ F) y) := by
  rw [← jet_hessian_actual F hF y, jetHessian, jet_second_actual]

theorem riesz_postcomposition_preserves_operator_norm (H : E →L[ℝ] E →L[ℝ] ℝ) :
    ‖(InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp H‖ = ‖H‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg H)
    intro v
    change ‖(InnerProductSpace.toDual ℝ E).symm (H v)‖ ≤ ‖H‖ * ‖v‖
    rw [(InnerProductSpace.toDual ℝ E).symm.norm_map]
    exact H.le_opNorm v
  · apply H.opNorm_le_bound (norm_nonneg _)
    intro v
    have hh := ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp H).le_opNorm v
    change ‖(InnerProductSpace.toDual ℝ E).symm (H v)‖ ≤ _ at hh
    rw [(InnerProductSpace.toDual ℝ E).symm.norm_map] at hh
    exact hh

theorem actual_hessian_norm_in_gradient_coordinates (F : E → ℝ) (hF : ContDiff ℝ 2 F) (y : E) :
    ‖fderiv ℝ (gradient F) y‖ = ‖fderiv ℝ (fderiv ℝ F) y‖ := by
  rw [gradient_hessian_is_actual_riesz_image F hF y, riesz_postcomposition_preserves_operator_norm]

theorem actual_hessian_difference_norm_in_gradient_coordinates
    (F : E → ℝ) (hF : ContDiff ℝ 2 F) (x y : E) :
    ‖fderiv ℝ (gradient F) x - fderiv ℝ (gradient F) y‖ =
      ‖fderiv ℝ (fderiv ℝ F) x - fderiv ℝ (fderiv ℝ F) y‖ := by
  rw [gradient_hessian_is_actual_riesz_image F hF x,
    gradient_hessian_is_actual_riesz_image F hF y, ← ContinuousLinearMap.comp_sub,
    riesz_postcomposition_preserves_operator_norm]

theorem jet_value_continuous : Continuous (jetValue : AllDerivativeResponse E → ℝ) :=
  (continuousMultilinearCurryFin0 ℝ E ℝ).continuous.comp (continuous_apply 0)

theorem jet_gradient_continuous : Continuous (jetGradient : AllDerivativeResponse E → E) :=
  (InnerProductSpace.toDual ℝ E).symm.continuous.comp
    ((continuousMultilinearCurryFin1 ℝ E ℝ).continuous.comp (continuous_apply 1))

theorem jet_second_continuous : Continuous (jetSecond : AllDerivativeResponse E → E →L[ℝ] E →L[ℝ] ℝ) :=
  (continuousMultilinearCurryFin1 ℝ E (E →L[ℝ] ℝ)).continuous.comp
    ((continuousMultilinearCurryRightEquiv' ℝ 1 E ℝ).continuous.comp (continuous_apply 2))

theorem jet_hessian_continuous : Continuous (jetHessian : AllDerivativeResponse E → E →L[ℝ] E) :=
  (continuous_const : Continuous (fun _ : AllDerivativeResponse E =>
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap)).clm_comp
      jet_second_continuous

def shiftFromJet (mu : ℝ) (r : AllDerivativeResponse E) : E :=
  -((2 * mu)⁻¹ • jetGradient r)

theorem shift_from_actual_zero_query (F : E → ℝ) (mu : ℝ) :
    shiftFromJet mu (allDerivativeOracle F 0) = initialShift F mu := by
  rw [shiftFromJet, jet_gradient_actual]
  rfl

theorem shift_from_jet_continuous (mu : ℝ) : Continuous (shiftFromJet mu : AllDerivativeResponse E → E) :=
  (jet_gradient_continuous.const_smul _).neg

def liftedBundleFromJet (mu b : ℝ) (c : E) (z : Joint E)
    (r : AllDerivativeResponse E) : SaddleResponse E :=
  simulateBundle mu b c z (jetValue r) (jetGradient r) (jetHessian r)

theorem simulator_jointly_continuous (mu b : ℝ) :
    Continuous (fun p : E × Joint E × ℝ × E × (E →L[ℝ] E) =>
      simulateBundle mu b p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  unfold simulateBundle
  fun_prop

theorem lifted_bundle_from_jet_jointly_continuous (mu b : ℝ) :
    Continuous (fun p : E × Joint E × AllDerivativeResponse E =>
      liftedBundleFromJet mu b p.1 p.2.1 p.2.2) := by
  have hc : Continuous (fun p : E × Joint E × AllDerivativeResponse E => p.1) := continuous_fst
  have hz : Continuous (fun p : E × Joint E × AllDerivativeResponse E => p.2.1) := continuous_fst.comp continuous_snd
  have hr : Continuous (fun p : E × Joint E × AllDerivativeResponse E => p.2.2) := continuous_snd.comp continuous_snd
  exact (simulator_jointly_continuous mu b).comp
    (hc.prodMk (hz.prodMk ((jet_value_continuous.comp hr).prodMk
      ((jet_gradient_continuous.comp hr).prodMk (jet_hessian_continuous.comp hr)))))

theorem actual_lifted_bundle_from_one_real_query (F : E → ℝ) (hF : ContDiff ℝ 2 F)
    (mu b : ℝ) (c : E) (z : Joint E) :
    liftedBundleFromJet mu b c z (allDerivativeOracle F z.snd) = actualBundle F mu b c z := by
  rw [liftedBundleFromJet, jet_value_actual, jet_gradient_actual, jet_hessian_actual F hF]
  exact one_query_bundle_simulation F hF mu b c z

end
end FangqingLiftOracleJetBridge
end

section
-- Source component: AllDerivativeLiftExecution.lean

open MeasureTheory
open scoped ContDiff

namespace FangqingAllDerivativeLiftExecution

open OriginalPrefixOracleReplay FangqingSingleLowerAllDerivativeOracle
  FangqingSingleLowerActualOracleProgram FangqingSingleLowerOracleRescaling
  FangqingSingleLowerFixedFunctionExecution FangqingSingleLowerAlgorithmMeasurability
  FangqingLiftOracleJetBridge AllDerivativeLift

noncomputable section
set_option maxHeartbeats 6000000

variable {Seed E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Literal saddle O2 execution on the single actual lift whose c is fixed by F. -/
def actualSaddleRun (F : E → ℝ) (mu b : ℝ)
    (q : Query Seed (SaddleResponse E) (Joint E)) : ℕ → Seed → State (SaddleResponse E)
  | 0, _ => (0, 0)
  | t + 1, seed =>
      let st := actualSaddleRun F mu b q t seed
      (t + 1, Function.update st.2 t
        (actualBundle F mu b (initialShift F mu) (q t seed st)))

def decodedState (mu b : ℝ) (q : Query Seed (SaddleResponse E) (Joint E)) :
    ℕ → Seed → (ℕ → AllDerivativeResponse E) → State (SaddleResponse E)
  | 0, _, _ => (0, 0)
  | t + 1, seed, h =>
      let st := decodedState mu b q t seed h
      let c := shiftFromJet mu (h 0)
      let z := q t seed st
      (t + 1, Function.update st.2 t (liftedBundleFromJet mu b c z (h (t + 1))))

/-- The very first paid F request is at zero; no c is supplied to the algorithm. -/
def sourceQuery (mu b : ℝ) (q : Query Seed (SaddleResponse E) (Joint E)) :
    Query Seed (AllDerivativeResponse E) E
  | 0, _, _ => 0
  | t + 1, seed, st => (q t seed (decodedState mu b q t seed st.2)).snd

def sourceOutput (mu b : ℝ) (q : Query Seed (SaddleResponse E) (Joint E))
    (out : Seed → State (SaddleResponse E) → E) (N : ℕ) :
    Seed → State (AllDerivativeResponse E) → E :=
  fun seed st => center b (shiftFromJet mu (st.2 0))
    (out seed (decodedState mu b q N seed st.2))

def actualBaseRun (F : E → ℝ) (mu b : ℝ)
    (q : Query Seed (SaddleResponse E) (Joint E)) (baseDimension : ℕ) (K : ℕ) (seed : Seed) :
    State (AllDerivativeResponse E) :=
  run (sourceQuery mu b q) (grantEveryResponse baseDimension)
    (familyReply (fun _ : Fin (baseDimension + 1) → E => F)) K seed 0

def saddleOutput (F : E → ℝ) (mu b : ℝ)
    (q : Query Seed (SaddleResponse E) (Joint E)) (out : Seed → State (SaddleResponse E) → E)
    (N : ℕ) (seed : Seed) : E := out seed (actualSaddleRun F mu b q N seed)

theorem first_source_query_is_zero (mu b : ℝ)
    (q : Query Seed (SaddleResponse E) (Joint E)) (seed : Seed)
    (st : State (AllDerivativeResponse E)) : sourceQuery mu b q 0 seed st = 0 := rfl

theorem decoded_state_depends_only_on_paid_prefix (mu b : ℝ)
    (q : Query Seed (SaddleResponse E) (Joint E)) (N : ℕ) (seed : Seed)
    (h k : ℕ → AllDerivativeResponse E) (hprefix : ∀ i ≤ N, h i = k i) :
    decodedState mu b q N seed h = decodedState mu b q N seed k := by
  induction N with
  | zero => rfl
  | succ N ih =>
      have hs := ih (fun i hi => hprefix i (by omega))
      simp only [decodedState, hs, hprefix 0 (by omega), hprefix (N + 1) (by omega)]

theorem decoded_state_unchanged_by_next_query_reply (mu b : ℝ)
    (q : Query Seed (SaddleResponse E) (Joint E)) (N : ℕ) (seed : Seed)
    (h : ℕ → AllDerivativeResponse E) (r : AllDerivativeResponse E) :
    decodedState mu b q N seed (Function.update h (N + 1) r) = decodedState mu b q N seed h := by
  apply decoded_state_depends_only_on_paid_prefix
  intro i hi
  simp only [Function.update_apply, show i ≠ N + 1 by omega, if_false]

theorem actual_bootstrap_response_is_preserved (F : E → ℝ) (mu b : ℝ)
    (q : Query Seed (SaddleResponse E) (Joint E)) (baseDimension N : ℕ) (seed : Seed) :
    (actualBaseRun F mu b q baseDimension (N + 1) seed).2 0 = allDerivativeOracle F 0 := by
  induction N with
  | zero =>
      change (Function.update (0 : ℕ → AllDerivativeResponse E) 0
        (allDerivativeOracle F (sourceQuery mu b q 0 seed (0, 0)))) 0 = _
      simp only [Function.update_self, sourceQuery]
  | succ N ih =>
      change (Function.update (actualBaseRun F mu b q baseDimension (N + 1) seed).2 (N + 1)
        (allDerivativeOracle F (sourceQuery mu b q (N + 1) seed
          (actualBaseRun F mu b q baseDimension (N + 1) seed)))) 0 = _
      rw [Function.update_of_ne (by omega : (0 : ℕ) ≠ N + 1)]
      exact ih

theorem actual_shift_is_computed_by_the_bootstrap_query (F : E → ℝ) (mu b : ℝ)
    (q : Query Seed (SaddleResponse E) (Joint E)) (baseDimension N : ℕ) (seed : Seed) :
    shiftFromJet mu ((actualBaseRun F mu b q baseDimension (N + 1) seed).2 0) = initialShift F mu := by
  rw [actual_bootstrap_response_is_preserved, shift_from_actual_zero_query]

/-- Every saddle value, gradient and full joint Hessian in the actual history
    is reconstructed from one real F(y) all-derivative response, after one F(0) call. -/
theorem actual_decoded_history_equals_the_single_fixed_lift_history
    (F : E → ℝ) (hF : ContDiff ℝ 2 F) (mu b : ℝ)
    (q : Query Seed (SaddleResponse E) (Joint E)) (baseDimension N : ℕ) (seed : Seed) :
    decodedState mu b q N seed (actualBaseRun F mu b q baseDimension (N + 1) seed).2 =
      actualSaddleRun F mu b q N seed := by
  induction N with
  | zero => rfl
  | succ N ih =>
      let st := actualBaseRun F mu b q baseDimension (N + 1) seed
      have hi : decodedState mu b q N seed st.2 = actualSaddleRun F mu b q N seed := ih
      have hc : shiftFromJet mu (st.2 0) = initialShift F mu :=
        actual_shift_is_computed_by_the_bootstrap_query F mu b q baseDimension N seed
      have hquery : sourceQuery mu b q (N + 1) seed st =
          (q N seed (actualSaddleRun F mu b q N seed)).snd := by
        simp only [sourceQuery, hi]
      change decodedState mu b q (N + 1) seed (Function.update st.2 (N + 1)
        (allDerivativeOracle F (sourceQuery mu b q (N + 1) seed st))) = _
      simp only [decodedState, decoded_state_unchanged_by_next_query_reply,
        Function.update_of_ne (by omega : (0 : ℕ) ≠ N + 1), Function.update_self, hi, hc, hquery,
        actual_lifted_bundle_from_one_real_query F hF, actualSaddleRun]

theorem actual_next_source_query_is_exactly_the_saddle_y_query
    (F : E → ℝ) (hF : ContDiff ℝ 2 F) (mu b : ℝ)
    (q : Query Seed (SaddleResponse E) (Joint E)) (baseDimension N : ℕ) (seed : Seed) :
    sourceQuery mu b q (N + 1) seed (actualBaseRun F mu b q baseDimension (N + 1) seed) =
      (q N seed (actualSaddleRun F mu b q N seed)).snd := by
  simp only [sourceQuery, actual_decoded_history_equals_the_single_fixed_lift_history F hF]

def actualSaddleQueryTrace (F : E → ℝ) (mu b : ℝ)
    (q : Query Seed (SaddleResponse E) (Joint E)) : ℕ → Seed → List (Joint E)
  | 0, _ => []
  | N + 1, seed => actualSaddleQueryTrace F mu b q N seed ++
      [q N seed (actualSaddleRun F mu b q N seed)]

/-- Actual paid source requests are exactly 0, followed by each actual saddle y. -/
theorem actual_source_query_trace_has_exactly_one_initialization_request
    (F : E → ℝ) (hF : ContDiff ℝ 2 F) (mu b : ℝ)
    (q : Query Seed (SaddleResponse E) (Joint E)) (baseDimension N : ℕ) (seed : Seed) :
    actualQueryTrace baseDimension (fun _ : Fin (baseDimension + 1) → E => F)
      (sourceQuery mu b q) (N + 1) seed 0 =
      (0 : E) :: (actualSaddleQueryTrace F mu b q N seed).map (fun z => z.snd) := by
  induction N with
  | zero => simp only [actualQueryTrace, sourceQuery, List.nil_append, actualSaddleQueryTrace, List.map_nil]
  | succ N ih =>
      change actualQueryTrace baseDimension (fun _ : Fin (baseDimension + 1) → E => F)
        (sourceQuery mu b q) (N + 1) seed 0 ++
        [sourceQuery mu b q (N + 1) seed (actualBaseRun F mu b q baseDimension (N + 1) seed)] = _
      rw [ih, actual_next_source_query_is_exactly_the_saddle_y_query F hF]
      simp only [actualSaddleQueryTrace, List.map_append, List.map_singleton, List.cons_append, List.nil_append]

theorem actual_source_output_is_the_center_of_the_actual_saddle_output
    (F : E → ℝ) (hF : ContDiff ℝ 2 F) (mu b : ℝ)
    (q : Query Seed (SaddleResponse E) (Joint E)) (out : Seed → State (SaddleResponse E) → E)
    (baseDimension N : ℕ) (seed : Seed) :
    outputOnFunction baseDimension (N + 1) (sourceQuery mu b q) (sourceOutput mu b q out N) F seed =
      center b (initialShift F mu) (saddleOutput F mu b q out N seed) := by
  change center b (shiftFromJet mu ((actualBaseRun F mu b q baseDimension (N + 1) seed).2 0))
    (out seed (decodedState mu b q N seed (actualBaseRun F mu b q baseDimension (N + 1) seed).2)) = _
  rw [actual_shift_is_computed_by_the_bootstrap_query,
    actual_decoded_history_equals_the_single_fixed_lift_history F hF]
  rfl

theorem source_actual_paid_query_count_is_saddle_budget_plus_one
    (F : E → ℝ) (mu b : ℝ) (q : Query Seed (SaddleResponse E) (Joint E))
    (baseDimension N : ℕ) (seed : Seed) :
    (actualQueryTrace baseDimension (fun _ : Fin (baseDimension + 1) → E => F)
      (sourceQuery mu b q) (N + 1) seed 0).length = N + 1 :=
  actualQueryTrace_length _ _ _ _ _ _

section BorelAlgorithm
variable [FiniteDimensional ℝ E] [MeasurableSpace Seed] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (Joint E)] [BorelSpace (Joint E)]
  [MeasurableSpace (SaddleResponse E)] [BorelSpace (SaddleResponse E)]
  [MeasurableSpace (AllDerivativeResponse E)] [BorelSpace (AllDerivativeResponse E)]

theorem decoded_state_measurable (mu b : ℝ)
    (q : Query Seed (SaddleResponse E) (Joint E))
    (hq : ∀ t, Measurable (fun x : Seed × State (SaddleResponse E) => q t x.1 x.2)) (N : ℕ) :
    Measurable (fun x : Seed × (ℕ → AllDerivativeResponse E) => decodedState mu b q N x.1 x.2) := by
  induction N with
  | zero => exact measurable_const
  | succ N ih =>
      have hz := (hq N).comp (measurable_fst.prodMk ih)
      have hc : Measurable (fun x : Seed × (ℕ → AllDerivativeResponse E) => shiftFromJet mu (x.2 0)) :=
        (shift_from_jet_continuous mu).measurable.comp ((measurable_pi_apply 0).comp measurable_snd)
      have hr : Measurable (fun x : Seed × (ℕ → AllDerivativeResponse E) => x.2 (N + 1)) :=
        (measurable_pi_apply (N + 1)).comp measurable_snd
      have ha := (lifted_bundle_from_jet_jointly_continuous mu b).measurable.comp
        (hc.prodMk (hz.prodMk hr))
      apply measurable_const.prodMk
      apply measurable_pi_lambda
      intro i
      by_cases hi : i = N
      · subst i
        convert! ha using 1
        funext x
        simp only [decodedState, Function.update_self, Function.comp_def]
      · convert! ((measurable_pi_apply i).comp (measurable_snd.comp ih)) using 1
        funext x
        simp only [decodedState, Function.update_apply, hi, if_false, Function.comp_def]

theorem source_query_measurable (mu b : ℝ)
    (q : Query Seed (SaddleResponse E) (Joint E))
    (hq : ∀ t, Measurable (fun x : Seed × State (SaddleResponse E) => q t x.1 x.2)) (t : ℕ) :
    Measurable (fun x : Seed × State (AllDerivativeResponse E) => sourceQuery mu b q t x.1 x.2) := by
  cases t with
  | zero => exact measurable_const
  | succ t =>
      have hs : Measurable (fun x : Seed × State (AllDerivativeResponse E) =>
          decodedState mu b q t x.1 x.2.2) :=
        (decoded_state_measurable mu b q hq t).comp
          (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
      exact (WithLp.sndL 2 ℝ E E).continuous.measurable.comp ((hq t).comp (measurable_fst.prodMk hs))

theorem source_output_measurable (mu b : ℝ)
    (q : Query Seed (SaddleResponse E) (Joint E))
    (hq : ∀ t, Measurable (fun x : Seed × State (SaddleResponse E) => q t x.1 x.2))
    (out : Seed → State (SaddleResponse E) → E)
    (hout : Measurable (fun x : Seed × State (SaddleResponse E) => out x.1 x.2)) (N : ℕ) :
    Measurable (fun x : Seed × State (AllDerivativeResponse E) => sourceOutput mu b q out N x.1 x.2) := by
  have hs : Measurable (fun x : Seed × State (AllDerivativeResponse E) =>
      decodedState mu b q N x.1 x.2.2) :=
    (decoded_state_measurable mu b q hq N).comp
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have hc : Measurable (fun x : Seed × State (AllDerivativeResponse E) => shiftFromJet mu (x.2.2 0)) :=
    (shift_from_jet_continuous mu).measurable.comp
      ((measurable_pi_apply 0).comp (measurable_snd.comp measurable_snd))
  exact ((hout.comp (measurable_fst.prodMk hs)).const_smul b).add hc

theorem actual_source_history_measurable (F : E → ℝ) (hF : ContDiff ℝ ∞ F) (mu b : ℝ)
    (q : Query Seed (SaddleResponse E) (Joint E))
    (hq : ∀ t, Measurable (fun x : Seed × State (SaddleResponse E) => q t x.1 x.2))
    (baseDimension K : ℕ) : Measurable (actualBaseRun F mu b q baseDimension K) := by
  have hh := run_measurable (sourceQuery mu b q) (grantEveryResponse baseDimension)
    (familyReply (fun _ : Fin (baseDimension + 1) → E => F))
    (source_query_measurable mu b q hq) (fun _ => measurable_const)
    (fixed_full_oracle_reply_measurable baseDimension F hF) K
  exact hh.comp (measurable_id.prodMk measurable_const)

theorem actual_saddle_history_measurable (F : E → ℝ) (hF : ContDiff ℝ ∞ F) (mu b : ℝ)
    (q : Query Seed (SaddleResponse E) (Joint E))
    (hq : ∀ t, Measurable (fun x : Seed × State (SaddleResponse E) => q t x.1 x.2))
    (baseDimension N : ℕ) : Measurable (actualSaddleRun F mu b q N) := by
  have hh := (decoded_state_measurable mu b q hq N).comp
    (measurable_id.prodMk (measurable_snd.comp (actual_source_history_measurable F hF mu b q hq baseDimension (N + 1))))
  convert! hh using 1
  funext seed
  exact (actual_decoded_history_equals_the_single_fixed_lift_history F
    (hF.of_le (by decide)) mu b q baseDimension N seed).symm

theorem actual_saddle_output_measurable (F : E → ℝ) (hF : ContDiff ℝ ∞ F) (mu b : ℝ)
    (q : Query Seed (SaddleResponse E) (Joint E))
    (hq : ∀ t, Measurable (fun x : Seed × State (SaddleResponse E) => q t x.1 x.2))
    (out : Seed → State (SaddleResponse E) → E)
    (hout : Measurable (fun x : Seed × State (SaddleResponse E) => out x.1 x.2)) (N : ℕ) :
    Measurable (saddleOutput F mu b q out N) :=
  hout.comp (measurable_id.prodMk (actual_saddle_history_measurable F hF mu b q hq 0 N))

end BorelAlgorithm

section Stationarity
variable [FiniteDimensional ℝ E]

theorem actual_algorithm_output_stationarity_transfer
    (F : E → ℝ) (hF : ContDiff ℝ 2 F) (mu b : ℝ) (hmu : 0 < mu) (hb : 0 < b)
    (hlip : ∀ y z : E, ‖gradient F y - gradient F z‖ ≤ mu * ‖y - z‖)
    (q : Query Seed (SaddleResponse E) (Joint E)) (out : Seed → State (SaddleResponse E) → E)
    (baseDimension N : ℕ) (seed : Seed) :
    ‖gradient F (outputOnFunction baseDimension (N + 1) (sourceQuery mu b q)
      (sourceOutput mu b q out N) F seed)‖ ≤
      (3 / (2 * b)) * ‖gradient (phi F mu b (initialShift F mu)) (saddleOutput F mu b q out N seed)‖ := by
  rw [actual_source_output_is_the_center_of_the_actual_saddle_output F hF]
  exact lift_stationarity_positive F mu b (initialShift F mu) hmu hb
    (hF.differentiable (by norm_num)) hlip _

theorem actual_algorithm_output_stationarity_from_actual_F_class
    (F : E → ℝ) (hF : ContDiff ℝ 2 F) (mu b : ℝ) (hmu : 0 < mu) (hb : 0 < b)
    (hH : ∀ y : E, ‖fderiv ℝ (fderiv ℝ F) y‖ ≤ mu)
    (q : Query Seed (SaddleResponse E) (Joint E)) (out : Seed → State (SaddleResponse E) → E)
    (baseDimension N : ℕ) (seed : Seed) :
    ‖gradient F (outputOnFunction baseDimension (N + 1) (sourceQuery mu b q)
      (sourceOutput mu b q out N) F seed)‖ ≤
      (3 / (2 * b)) * ‖gradient (phi F mu b (initialShift F mu)) (saddleOutput F mu b q out N seed)‖ := by
  apply actual_algorithm_output_stationarity_transfer F hF mu b hmu hb
  apply gradient_lipschitz_from_hessian_norm F hF mu
  intro y
  rw [actual_hessian_norm_in_gradient_coordinates F hF y]
  exact hH y

theorem actual_saddle_success_is_source_success
    (F : E → ℝ) (hF : ContDiff ℝ 2 F) (mu b eps : ℝ) (hmu : 0 < mu) (hb : 0 < b)
    (hH : ∀ y : E, ‖fderiv ℝ (fderiv ℝ F) y‖ ≤ mu)
    (q : Query Seed (SaddleResponse E) (Joint E)) (out : Seed → State (SaddleResponse E) → E)
    (baseDimension N : ℕ) :
    {seed | ‖gradient (phi F mu b (initialShift F mu)) (saddleOutput F mu b q out N seed)‖ ≤ eps} ⊆
      {seed | ‖gradient F (outputOnFunction baseDimension (N + 1) (sourceQuery mu b q)
        (sourceOutput mu b q out N) F seed)‖ ≤ (3 / (2 * b)) * eps} := by
  intro seed hsuccess
  exact (actual_algorithm_output_stationarity_from_actual_F_class F hF mu b hmu hb hH q out
    baseDimension N seed).trans (mul_le_mul_of_nonneg_left hsuccess (by positivity))

theorem actual_saddle_success_probability_le_source_success
    [MeasurableSpace Seed] (seeds : Measure Seed)
    (F : E → ℝ) (hF : ContDiff ℝ 2 F) (mu b eps : ℝ) (hmu : 0 < mu) (hb : 0 < b)
    (hH : ∀ y : E, ‖fderiv ℝ (fderiv ℝ F) y‖ ≤ mu)
    (q : Query Seed (SaddleResponse E) (Joint E)) (out : Seed → State (SaddleResponse E) → E)
    (baseDimension N : ℕ) :
    seeds {seed | ‖gradient (phi F mu b (initialShift F mu)) (saddleOutput F mu b q out N seed)‖ ≤ eps} ≤
      seeds {seed | ‖gradient F (outputOnFunction baseDimension (N + 1) (sourceQuery mu b q)
        (sourceOutput mu b q out N) F seed)‖ ≤ (3 / (2 * b)) * eps} :=
  measure_mono (actual_saddle_success_is_source_success F hF mu b eps hmu hb hH q out baseDimension N)

end Stationarity

section CompleteAlgorithmReduction
variable [FiniteDimensional ℝ E] [MeasurableSpace Seed] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (Joint E)] [BorelSpace (Joint E)]
  [MeasurableSpace (SaddleResponse E)] [BorelSpace (SaddleResponse E)]
  [MeasurableSpace (AllDerivativeResponse E)] [BorelSpace (AllDerivativeResponse E)]

/-- Full fixed-instance algorithm reduction, with an actual charged F(0)
    bootstrap and exact one-for-one subsequent queries and terminal output. -/
theorem actual_borel_lift_algorithm_reduction (seeds : Measure Seed)
    (F : E → ℝ) (hF : ContDiff ℝ ∞ F) (mu b eps : ℝ) (hmu : 0 < mu) (hb : 0 < b)
    (hH : ∀ y : E, ‖fderiv ℝ (fderiv ℝ F) y‖ ≤ mu)
    (q : Query Seed (SaddleResponse E) (Joint E))
    (hq : ∀ t, Measurable (fun x : Seed × State (SaddleResponse E) => q t x.1 x.2))
    (out : Seed → State (SaddleResponse E) → E)
    (hout : Measurable (fun x : Seed × State (SaddleResponse E) => out x.1 x.2))
    (baseDimension N : ℕ) :
    (∀ t, Measurable (fun x : Seed × State (AllDerivativeResponse E) => sourceQuery mu b q t x.1 x.2)) ∧
      Measurable (fun x : Seed × State (AllDerivativeResponse E) => sourceOutput mu b q out N x.1 x.2) ∧
      Measurable (actualSaddleRun F mu b q N) ∧
      (∀ seed, decodedState mu b q N seed (actualBaseRun F mu b q baseDimension (N + 1) seed).2 =
        actualSaddleRun F mu b q N seed) ∧
      (∀ seed, outputOnFunction baseDimension (N + 1) (sourceQuery mu b q) (sourceOutput mu b q out N) F seed =
        center b (initialShift F mu) (saddleOutput F mu b q out N seed)) ∧
      (∀ seed, actualQueryTrace baseDimension (fun _ : Fin (baseDimension + 1) → E => F)
        (sourceQuery mu b q) (N + 1) seed 0 =
          (0 : E) :: (actualSaddleQueryTrace F mu b q N seed).map (fun z => z.snd)) ∧
      (∀ seed, (actualQueryTrace baseDimension (fun _ : Fin (baseDimension + 1) → E => F)
        (sourceQuery mu b q) (N + 1) seed 0).length = N + 1) ∧
      seeds {seed | ‖gradient (phi F mu b (initialShift F mu)) (saddleOutput F mu b q out N seed)‖ ≤ eps} ≤
        seeds {seed | ‖gradient F (outputOnFunction baseDimension (N + 1) (sourceQuery mu b q)
          (sourceOutput mu b q out N) F seed)‖ ≤ (3 / (2 * b)) * eps} := by
  have h2 : ContDiff ℝ 2 F := hF.of_le (by decide)
  exact ⟨source_query_measurable mu b q hq, source_output_measurable mu b q hq out hout N,
    actual_saddle_history_measurable F hF mu b q hq baseDimension N,
    actual_decoded_history_equals_the_single_fixed_lift_history F h2 mu b q baseDimension N,
    actual_source_output_is_the_center_of_the_actual_saddle_output F h2 mu b q out baseDimension N,
    actual_source_query_trace_has_exactly_one_initialization_request F h2 mu b q baseDimension N,
    source_actual_paid_query_count_is_saddle_budget_plus_one F mu b q baseDimension N,
    actual_saddle_success_probability_le_source_success seeds F h2 mu b eps hmu hb hH q out baseDimension N⟩

end CompleteAlgorithmReduction

end
end FangqingAllDerivativeLiftExecution
end

section
-- Source component: DecoupledLowerLift.lean

open scoped ContDiff

namespace FangqingDecoupledLowerLift

open FangqingLiftOracleJetBridge JointSliceRegularity AllDerivativeLift

noncomputable section
set_option maxHeartbeats 6000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def objective (F : E → ℝ) (mu : ℝ) (z : Joint E) : ℝ :=
  F z.fst - mu / 2 * ‖z.snd‖ ^ 2

def slice (F : E → ℝ) (mu : ℝ) (x y : E) : ℝ := F x - mu / 2 * ‖y‖ ^ 2

def value (F : E → ℝ) (mu : ℝ) (x : E) : ℝ := sSup (Set.range (slice F mu x))

def blockHessian (H : E →L[ℝ] E) (mu : ℝ) : Joint E →L[ℝ] Joint E :=
  ((axisX (E := E) (F := E)).toContinuousLinearMap.comp H).comp (WithLp.fstL 2 ℝ E E) -
    mu • ((axisY (E := E) (F := E)).toContinuousLinearMap.comp (WithLp.sndL 2 ℝ E E))

theorem objective_is_slice (F : E → ℝ) (mu : ℝ) (x y : E) :
    objective F mu (point x y) = slice F mu x y := by
  rw [point_eq_toLp]
  rfl

theorem objective_C2 (F : E → ℝ) (hF : ContDiff ℝ 2 F) (mu : ℝ) :
    ContDiff ℝ 2 (objective F mu) :=
  (hF.comp (WithLp.fstL 2 ℝ E E).contDiff).sub
    (contDiff_const.mul ((WithLp.sndL 2 ℝ E E).contDiff.norm_sq ℝ))

theorem actual_gradient (F : E → ℝ) (hF : Differentiable ℝ F) (mu : ℝ) (z : Joint E) :
    gradient (objective F mu) z = point (gradient F z.fst) (-mu • z.snd) := by
  have hp := (hF z.fst).hasFDerivAt.comp z (WithLp.fstL 2 ℝ E E).hasFDerivAt
  have hq := ((WithLp.sndL 2 ℝ E E).hasFDerivAt (x := z)).norm_sq.const_mul (mu / 2)
  have hd := hp.sub hq
  have hg : HasGradientAt (objective F mu) (point (gradient F z.fst) (-mu • z.snd)) z := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert! hd using 1
    ext v
    simp only [InnerProductSpace.toDual_apply_apply, point_eq_toLp, WithLp.prod_inner_apply,
      WithLp.ofLp_toLp, Prod.fst, Prod.snd, real_inner_smul_left, inner_gradient_left,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      WithLp.fstL_apply, WithLp.sndL_apply, innerSL_apply_apply, smul_eq_mul]
    simp only [WithLp.fst, WithLp.snd, two_smul]
    ring
  exact hg.gradient

theorem blockHessian_apply (H : E →L[ℝ] E) (mu : ℝ) (v : Joint E) :
    blockHessian H mu v = point (H v.fst) (-mu • v.snd) := by
  apply (WithLp.ext_iff 2).mpr
  simp [blockHessian, point, axisX, axisY, neg_smul]

theorem actual_hessian (F : E → ℝ) (hF : ContDiff ℝ 2 F) (mu : ℝ) (z : Joint E) :
    fderiv ℝ (gradient (objective F mu)) z = blockHessian (fderiv ℝ (gradient F) z.fst) mu := by
  have hgrad : gradient (objective F mu) = fun w =>
      axisX (F := E) (gradient F w.fst) - mu • axisY (E := E) w.snd := by
    funext w
    rw [actual_gradient F (hF.differentiable (by norm_num)) mu w]
    apply (WithLp.ext_iff 2).mpr
    simp [point, axisX, axisY, neg_smul]
  have hfirst := (axisX (E := E) (F := E)).toContinuousLinearMap.hasFDerivAt.comp z
    (((gradient_differentiable F hF) z.fst).hasFDerivAt.comp z (WithLp.fstL 2 ℝ E E).hasFDerivAt)
  have hlast := ((axisY (E := E) (F := E)).toContinuousLinearMap.hasFDerivAt.comp z
    (WithLp.sndL 2 ℝ E E).hasFDerivAt).const_smul mu
  rw [hgrad]
  convert! (hfirst.sub hlast).fderiv using 1

theorem block_hessian_max_norm_bound (H : E →L[ℝ] E) (mu L : ℝ)
    (hmu : 0 ≤ mu) (hmL : mu ≤ L) (hH : ‖H‖ ≤ L) : ‖blockHessian H mu‖ ≤ L := by
  have hL : 0 ≤ L := hmu.trans hmL
  apply ContinuousLinearMap.opNorm_le_bound _ hL
  intro v
  have ha : ‖H v.fst‖ ≤ L * ‖v.fst‖ := (H.le_opNorm _).trans
    (mul_le_mul_of_nonneg_right hH (norm_nonneg _))
  have hb : ‖-mu • v.snd‖ ≤ L * ‖v.snd‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hmu]
    exact mul_le_mul_of_nonneg_right hmL (norm_nonneg _)
  have hsqA : ‖H v.fst‖ ^ 2 ≤ (L * ‖v.fst‖) ^ 2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr ha
  have hsqB : ‖-mu • v.snd‖ ^ 2 ≤ (L * ‖v.snd‖) ^ 2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hb
  have hn := WithLp.prod_norm_sq_eq_of_L2 v
  have ho : ‖point (H v.fst) (-mu • v.snd)‖ ^ 2 = ‖H v.fst‖ ^ 2 + ‖-mu • v.snd‖ ^ 2 := by
    rw [point_eq_toLp]
    exact WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (H v.fst, -mu • v.snd))
  have hnL := congrArg (fun t : ℝ => L ^ 2 * t) hn
  rw [blockHessian_apply]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ L * ‖v‖)).mp
  nlinarith only [hsqA, hsqB, hnL, ho]

theorem block_hessian_difference_norm_bound (H K : E →L[ℝ] E) (mu : ℝ) :
    ‖blockHessian H mu - blockHessian K mu‖ ≤ ‖H - K‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  have he : (blockHessian H mu - blockHessian K mu) v = axisX (F := E) ((H - K) v.fst) := by
    rw [ContinuousLinearMap.sub_apply, blockHessian_apply, blockHessian_apply]
    apply (WithLp.ext_iff 2).mpr
    simp [point, axisX, axisY, ContinuousLinearMap.sub_apply]

  rw [he, (axisX (E := E) (F := E)).norm_map]
  exact ((H - K).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (norm_fst_projection v) (norm_nonneg _))

theorem actual_joint_hessian_norm (F : E → ℝ) (hF : ContDiff ℝ 2 F) (mu L : ℝ)
    (hmu : 0 ≤ mu) (hmL : mu ≤ L) (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ L) (z : Joint E) :
    ‖fderiv ℝ (gradient (objective F mu)) z‖ ≤ L := by
  rw [actual_hessian F hF]
  apply block_hessian_max_norm_bound _ mu L hmu hmL
  rw [actual_hessian_norm_in_gradient_coordinates F hF]
  exact hH _

theorem actual_joint_hessian_lipschitz (F : E → ℝ) (hF : ContDiff ℝ 2 F) (mu rho : ℝ)
    (hrho : 0 ≤ rho)
    (hH : ∀ x y, ‖fderiv ℝ (fderiv ℝ F) x - fderiv ℝ (fderiv ℝ F) y‖ ≤ rho * ‖x - y‖)
    (z w : Joint E) :
    ‖fderiv ℝ (gradient (objective F mu)) z - fderiv ℝ (gradient (objective F mu)) w‖ ≤ rho * ‖z - w‖ := by
  rw [actual_hessian F hF, actual_hessian F hF]
  apply (block_hessian_difference_norm_bound _ _ mu).trans
  rw [actual_hessian_difference_norm_in_gradient_coordinates F hF]
  exact (hH _ _).trans (mul_le_mul_of_nonneg_left (norm_fst_projection_sub z w) hrho)

theorem inner_maximum_is_exactly_zero (F : E → ℝ) (mu : ℝ) (hmu : 0 < mu) (x : E) :
    (∀ y, slice F mu x y ≤ slice F mu x 0) ∧
      (∀ y, (∀ v, slice F mu x v ≤ slice F mu x y) → y = 0) := by
  constructor
  · intro y
    simp only [slice, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_zero]
    have hn : 0 ≤ mu / 2 * ‖y‖ ^ 2 := by positivity
    linarith
  · intro y hy
    have hh := hy 0
    simp only [slice, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_zero] at hh
    have hn : ‖y‖ ^ 2 = 0 := by nlinarith only [hh, sq_nonneg ‖y‖, hmu]
    exact norm_eq_zero.mp (by nlinarith only [hn, norm_nonneg y])

theorem actual_value_equals_F (F : E → ℝ) (mu : ℝ) (hmu : 0 ≤ mu) : value F mu = F := by
  funext x
  have hb : BddAbove (Set.range (slice F mu x)) := by
    refine ⟨F x, ?_⟩
    rintro v ⟨y, rfl⟩
    have hn : 0 ≤ mu / 2 * ‖y‖ ^ 2 := by positivity
    dsimp only [slice]
    linarith
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro v ⟨y, rfl⟩
    have hn : 0 ≤ mu / 2 * ‖y‖ ^ 2 := by positivity
    dsimp only [slice]
    linarith
  · apply le_csSup hb
    exact ⟨0, by simp [slice]⟩

theorem actual_initial_gap (F : E → ℝ) (mu Delta : ℝ) (hmu : 0 ≤ mu)
    (hgap : F 0 - sInf (Set.range F) ≤ Delta) :
    value F mu 0 - sInf (Set.range (value F mu)) ≤ Delta := by
  rw [actual_value_equals_F F mu hmu]
  exact hgap

theorem actual_strong_concavity (F : E → ℝ) (mu : ℝ) (x : E) :
    StrongConcaveOn (Set.univ : Set E) mu (slice F mu x) := by
  have hc : StrongConvexOn (Set.univ : Set E) mu (fun y => -slice F mu x y) := by
    rw [strongConvexOn_iff_convex]
    convert! (convexOn_const (-F x) convex_univ : ConvexOn ℝ (Set.univ : Set E) (fun _ : E => -F x)) using 1
    funext y
    simp only [slice]
    ring
  have hh := UniformConvexOn.neg hc
  have he : (-(fun y : E => -slice F mu x y)) = slice F mu x := by
    funext y
    simp only [Pi.neg_apply, neg_neg]
  rw [he] at hh
  exact hh

section Class
variable [FiniteDimensional ℝ E]

theorem actual_class_and_exact_normalization (F : E → ℝ) (hF : ContDiff ℝ 2 F)
    (mu L rho Delta : ℝ) (hmu : 0 < mu) (hmL : mu ≤ L) (hrho : 0 ≤ rho)
    (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ L)
    (hHLip : ∀ x y, ‖fderiv ℝ (fderiv ℝ F) x - fderiv ℝ (fderiv ℝ F) y‖ ≤ rho * ‖x - y‖)
    (hgap : F 0 - sInf (Set.range F) ≤ Delta) :
    ContDiff ℝ 2 (objective F mu) ∧
      (∀ x, StrongConcaveOn (Set.univ : Set E) mu (slice F mu x)) ∧
      (∀ z w, ‖gradient (objective F mu) z - gradient (objective F mu) w‖ ≤ L * ‖z - w‖) ∧
      (∀ z, ‖fderiv ℝ (gradient (objective F mu)) z‖ ≤ L) ∧
      (∀ z w, ‖fderiv ℝ (gradient (objective F mu)) z - fderiv ℝ (gradient (objective F mu)) w‖ ≤ rho * ‖z - w‖) ∧
      (∀ x, (∀ y, slice F mu x y ≤ slice F mu x 0) ∧
        (∀ y, (∀ v, slice F mu x v ≤ slice F mu x y) → y = 0)) ∧
      value F mu = F ∧ value F mu 0 - sInf (Set.range (value F mu)) ≤ Delta := by
  have hJ := objective_C2 F hF mu
  have hnorm := actual_joint_hessian_norm F hF mu L hmu.le hmL hH
  exact ⟨hJ, actual_strong_concavity F mu,
    gradient_lipschitz_from_hessian_norm (objective F mu) hJ L hnorm, hnorm,
    actual_joint_hessian_lipschitz F hF mu rho hrho hHLip,
    inner_maximum_is_exactly_zero F mu hmu, actual_value_equals_F F mu hmu.le,
    actual_initial_gap F mu Delta hmu.le hgap⟩

end Class
end
end FangqingDecoupledLowerLift
end

section
-- Source component: DecoupledLowerLiftExecution.lean

open MeasureTheory
open scoped ContDiff

namespace FangqingDecoupledLowerLiftExecution

open OriginalPrefixOracleReplay FangqingSingleLowerAllDerivativeOracle
  FangqingSingleLowerActualOracleProgram FangqingSingleLowerOracleRescaling
  FangqingSingleLowerFixedFunctionExecution FangqingSingleLowerAlgorithmMeasurability
  FangqingLiftOracleJetBridge FangqingDecoupledLowerLift JointSliceRegularity

noncomputable section
set_option maxHeartbeats 6000000

variable {Seed E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def actualBundle (F : E → ℝ) (mu : ℝ) (z : Joint E) : SaddleResponse E :=
  (objective F mu z, gradient (objective F mu) z, fderiv ℝ (gradient (objective F mu)) z)

def bundleFromJet (mu : ℝ) (z : Joint E) (r : AllDerivativeResponse E) : SaddleResponse E :=
  (jetValue r - mu / 2 * ‖z.snd‖ ^ 2,
    point (jetGradient r) (-mu • z.snd), blockHessian (jetHessian r) mu)

theorem actual_bundle_from_one_real_F_query (F : E → ℝ) (hF : ContDiff ℝ 2 F)
    (mu : ℝ) (z : Joint E) :
    bundleFromJet mu z (allDerivativeOracle F z.fst) = actualBundle F mu z := by
  rw [bundleFromJet, jet_value_actual, jet_gradient_actual, jet_hessian_actual F hF]
  unfold actualBundle
  rw [actual_gradient F (hF.differentiable (by norm_num)), actual_hessian F hF]
  rfl

theorem bundle_from_jet_jointly_continuous (mu : ℝ) :
    Continuous (fun p : Joint E × AllDerivativeResponse E => bundleFromJet mu p.1 p.2) := by
  have hV : Continuous (fun p : Joint E × AllDerivativeResponse E => jetValue p.2) :=
    jet_value_continuous.comp continuous_snd
  have hG : Continuous (fun p : Joint E × AllDerivativeResponse E => jetGradient p.2) :=
    jet_gradient_continuous.comp continuous_snd
  have hH : Continuous (fun p : Joint E × AllDerivativeResponse E => jetHessian p.2) :=
    jet_hessian_continuous.comp continuous_snd
  unfold bundleFromJet blockHessian point
  fun_prop

def actualSaddleRun (F : E → ℝ) (mu : ℝ)
    (q : Query Seed (SaddleResponse E) (Joint E)) : ℕ → Seed → State (SaddleResponse E)
  | 0, _ => (0, 0)
  | N + 1, seed =>
      let st := actualSaddleRun F mu q N seed
      (N + 1, Function.update st.2 N (actualBundle F mu (q N seed st)))

def decodedState (mu : ℝ) (q : Query Seed (SaddleResponse E) (Joint E)) :
    ℕ → Seed → (ℕ → AllDerivativeResponse E) → State (SaddleResponse E)
  | 0, _, _ => (0, 0)
  | N + 1, seed, h =>
      let st := decodedState mu q N seed h
      (N + 1, Function.update st.2 N (bundleFromJet mu (q N seed st) (h N)))

def sourceQuery (mu : ℝ) (q : Query Seed (SaddleResponse E) (Joint E)) : Query Seed (AllDerivativeResponse E) E :=
  fun t seed st => (q t seed (decodedState mu q t seed st.2)).fst

def sourceOutput (mu : ℝ) (q : Query Seed (SaddleResponse E) (Joint E))
    (out : Seed → State (SaddleResponse E) → E) (N : ℕ) : Seed → State (AllDerivativeResponse E) → E :=
  fun seed st => out seed (decodedState mu q N seed st.2)

def actualBaseRun (F : E → ℝ) (mu : ℝ) (q : Query Seed (SaddleResponse E) (Joint E))
    (baseDimension K : ℕ) (seed : Seed) : State (AllDerivativeResponse E) :=
  run (sourceQuery mu q) (grantEveryResponse baseDimension)
    (familyReply (fun _ : Fin (baseDimension + 1) → E => F)) K seed 0

def saddleOutput (F : E → ℝ) (mu : ℝ) (q : Query Seed (SaddleResponse E) (Joint E))
    (out : Seed → State (SaddleResponse E) → E) (N : ℕ) (seed : Seed) : E :=
  out seed (actualSaddleRun F mu q N seed)

def actualSaddleQueryTrace (F : E → ℝ) (mu : ℝ) (q : Query Seed (SaddleResponse E) (Joint E)) :
    ℕ → Seed → List (Joint E)
  | 0, _ => []
  | N + 1, seed => actualSaddleQueryTrace F mu q N seed ++ [q N seed (actualSaddleRun F mu q N seed)]

theorem decoded_state_depends_only_on_past (mu : ℝ) (q : Query Seed (SaddleResponse E) (Joint E))
    (N : ℕ) (seed : Seed) (h k : ℕ → AllDerivativeResponse E) (hp : ∀ i < N, h i = k i) :
    decodedState mu q N seed h = decodedState mu q N seed k := by
  induction N with
  | zero => rfl
  | succ N ih =>
      have hs := ih (fun i hi => hp i (by omega))
      simp only [decodedState, hs, hp N (by omega)]

theorem decoded_state_unchanged_by_new_reply (mu : ℝ) (q : Query Seed (SaddleResponse E) (Joint E))
    (N : ℕ) (seed : Seed) (h : ℕ → AllDerivativeResponse E) (r : AllDerivativeResponse E) :
    decodedState mu q N seed (Function.update h N r) = decodedState mu q N seed h := by
  apply decoded_state_depends_only_on_past
  intro i hi
  simp only [Function.update_apply, ne_of_lt hi, if_false]

theorem actual_decoded_history_is_single_fixed_decoupled_history (F : E → ℝ) (hF : ContDiff ℝ 2 F)
    (mu : ℝ) (q : Query Seed (SaddleResponse E) (Joint E)) (baseDimension N : ℕ) (seed : Seed) :
    decodedState mu q N seed (actualBaseRun F mu q baseDimension N seed).2 = actualSaddleRun F mu q N seed := by
  induction N with
  | zero => rfl
  | succ N ih =>
      let st := actualBaseRun F mu q baseDimension N seed
      have hi : decodedState mu q N seed st.2 = actualSaddleRun F mu q N seed := ih
      have hq : sourceQuery mu q N seed st = (q N seed (actualSaddleRun F mu q N seed)).fst := by
        simp only [sourceQuery, hi]
      change decodedState mu q (N + 1) seed (Function.update st.2 N
        (allDerivativeOracle F (sourceQuery mu q N seed st))) = _
      simp only [decodedState, decoded_state_unchanged_by_new_reply, Function.update_self,
        hi, hq, actual_bundle_from_one_real_F_query F hF, actualSaddleRun]

theorem actual_source_query_is_the_saddle_x_query (F : E → ℝ) (hF : ContDiff ℝ 2 F)
    (mu : ℝ) (q : Query Seed (SaddleResponse E) (Joint E)) (baseDimension N : ℕ) (seed : Seed) :
    sourceQuery mu q N seed (actualBaseRun F mu q baseDimension N seed) =
      (q N seed (actualSaddleRun F mu q N seed)).fst := by
  simp only [sourceQuery, actual_decoded_history_is_single_fixed_decoupled_history F hF]

theorem actual_source_output_is_same_unqueried_point (F : E → ℝ) (hF : ContDiff ℝ 2 F)
    (mu : ℝ) (q : Query Seed (SaddleResponse E) (Joint E)) (out : Seed → State (SaddleResponse E) → E)
    (baseDimension N : ℕ) (seed : Seed) :
    outputOnFunction baseDimension N (sourceQuery mu q) (sourceOutput mu q out N) F seed =
      saddleOutput F mu q out N seed := by
  change out seed (decodedState mu q N seed (actualBaseRun F mu q baseDimension N seed).2) = _
  rw [actual_decoded_history_is_single_fixed_decoupled_history F hF]
  rfl

theorem actual_source_query_trace_has_no_initialization_request (F : E → ℝ) (hF : ContDiff ℝ 2 F)
    (mu : ℝ) (q : Query Seed (SaddleResponse E) (Joint E)) (baseDimension N : ℕ) (seed : Seed) :
    actualQueryTrace baseDimension (fun _ : Fin (baseDimension + 1) → E => F) (sourceQuery mu q) N seed 0 =
      (actualSaddleQueryTrace F mu q N seed).map (fun z => z.fst) := by
  induction N with
  | zero => rfl
  | succ N ih =>
      change actualQueryTrace baseDimension (fun _ : Fin (baseDimension + 1) → E => F) (sourceQuery mu q) N seed 0 ++
        [sourceQuery mu q N seed (actualBaseRun F mu q baseDimension N seed)] = _
      rw [ih, actual_source_query_is_the_saddle_x_query F hF]
      simp only [actualSaddleQueryTrace, List.map_append, List.map_singleton]

theorem actual_paid_query_count_is_exactly_N (F : E → ℝ) (mu : ℝ)
    (q : Query Seed (SaddleResponse E) (Joint E)) (baseDimension N : ℕ) (seed : Seed) :
    (actualQueryTrace baseDimension (fun _ : Fin (baseDimension + 1) → E => F) (sourceQuery mu q) N seed 0).length = N :=
  actualQueryTrace_length _ _ _ _ _ _

section Borel
variable [FiniteDimensional ℝ E] [MeasurableSpace Seed] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (Joint E)] [BorelSpace (Joint E)]
  [MeasurableSpace (SaddleResponse E)] [BorelSpace (SaddleResponse E)]
  [MeasurableSpace (AllDerivativeResponse E)] [BorelSpace (AllDerivativeResponse E)]

theorem decoded_state_measurable (mu : ℝ) (q : Query Seed (SaddleResponse E) (Joint E))
    (hq : ∀ t, Measurable (fun x : Seed × State (SaddleResponse E) => q t x.1 x.2)) (N : ℕ) :
    Measurable (fun x : Seed × (ℕ → AllDerivativeResponse E) => decodedState mu q N x.1 x.2) := by
  induction N with
  | zero => exact measurable_const
  | succ N ih =>
      have hz := (hq N).comp (measurable_fst.prodMk ih)
      have hr : Measurable (fun x : Seed × (ℕ → AllDerivativeResponse E) => x.2 N) :=
        (measurable_pi_apply N).comp measurable_snd
      have ha := (bundle_from_jet_jointly_continuous mu).measurable.comp (hz.prodMk hr)
      apply measurable_const.prodMk
      apply measurable_pi_lambda
      intro i
      by_cases hi : i = N
      · subst i
        convert! ha using 1
        funext x
        simp only [decodedState, Function.update_self, Function.comp_def]
      · convert! ((measurable_pi_apply i).comp (measurable_snd.comp ih)) using 1
        funext x
        simp only [decodedState, Function.update_apply, hi, if_false, Function.comp_def]

theorem source_query_measurable (mu : ℝ) (q : Query Seed (SaddleResponse E) (Joint E))
    (hq : ∀ t, Measurable (fun x : Seed × State (SaddleResponse E) => q t x.1 x.2)) (t : ℕ) :
    Measurable (fun x : Seed × State (AllDerivativeResponse E) => sourceQuery mu q t x.1 x.2) := by
  have hs : Measurable (fun x : Seed × State (AllDerivativeResponse E) => decodedState mu q t x.1 x.2.2) :=
    (decoded_state_measurable mu q hq t).comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  exact (WithLp.fstL 2 ℝ E E).continuous.measurable.comp ((hq t).comp (measurable_fst.prodMk hs))

theorem source_output_measurable (mu : ℝ) (q : Query Seed (SaddleResponse E) (Joint E))
    (hq : ∀ t, Measurable (fun x : Seed × State (SaddleResponse E) => q t x.1 x.2))
    (out : Seed → State (SaddleResponse E) → E)
    (hout : Measurable (fun x : Seed × State (SaddleResponse E) => out x.1 x.2)) (N : ℕ) :
    Measurable (fun x : Seed × State (AllDerivativeResponse E) => sourceOutput mu q out N x.1 x.2) :=
  hout.comp (measurable_fst.prodMk ((decoded_state_measurable mu q hq N).comp
    (measurable_fst.prodMk (measurable_snd.comp measurable_snd))))

theorem actual_source_history_measurable (F : E → ℝ) (hF : ContDiff ℝ ∞ F) (mu : ℝ)
    (q : Query Seed (SaddleResponse E) (Joint E))
    (hq : ∀ t, Measurable (fun x : Seed × State (SaddleResponse E) => q t x.1 x.2))
    (baseDimension N : ℕ) : Measurable (actualBaseRun F mu q baseDimension N) := by
  have hb := run_measurable (sourceQuery mu q) (grantEveryResponse baseDimension)
    (familyReply (fun _ : Fin (baseDimension + 1) → E => F)) (source_query_measurable mu q hq)
    (fun _ => measurable_const) (fixed_full_oracle_reply_measurable baseDimension F hF) N
  exact hb.comp (measurable_id.prodMk measurable_const)

theorem actual_saddle_history_measurable (F : E → ℝ) (hF : ContDiff ℝ ∞ F) (mu : ℝ)
    (q : Query Seed (SaddleResponse E) (Joint E))
    (hq : ∀ t, Measurable (fun x : Seed × State (SaddleResponse E) => q t x.1 x.2))
    (baseDimension N : ℕ) : Measurable (actualSaddleRun F mu q N) := by
  have hb := run_measurable (sourceQuery mu q) (grantEveryResponse baseDimension)
    (familyReply (fun _ : Fin (baseDimension + 1) → E => F)) (source_query_measurable mu q hq)
    (fun _ => measurable_const) (fixed_full_oracle_reply_measurable baseDimension F hF) N
  have hb0 : Measurable (actualBaseRun F mu q baseDimension N) :=
    hb.comp (measurable_id.prodMk measurable_const)
  have hh := (decoded_state_measurable mu q hq N).comp
    (measurable_id.prodMk (measurable_snd.comp hb0))
  convert! hh using 1
  funext seed
  exact (actual_decoded_history_is_single_fixed_decoupled_history F (hF.of_le (by decide)) mu q baseDimension N seed).symm

theorem actual_saddle_output_measurable (F : E → ℝ) (hF : ContDiff ℝ ∞ F) (mu : ℝ)
    (q : Query Seed (SaddleResponse E) (Joint E))
    (hq : ∀ t, Measurable (fun x : Seed × State (SaddleResponse E) => q t x.1 x.2))
    (out : Seed → State (SaddleResponse E) → E)
    (hout : Measurable (fun x : Seed × State (SaddleResponse E) => out x.1 x.2)) (N : ℕ) :
    Measurable (saddleOutput F mu q out N) :=
  hout.comp (measurable_id.prodMk (actual_saddle_history_measurable F hF mu q hq 0 N))

end Borel

theorem actual_success_event_is_the_same_source_event (F : E → ℝ) (hF : ContDiff ℝ 2 F)
    (mu eps : ℝ) (hmu : 0 ≤ mu) (q : Query Seed (SaddleResponse E) (Joint E))
    (out : Seed → State (SaddleResponse E) → E) (baseDimension N : ℕ) :
    {seed | ‖gradient (value F mu) (saddleOutput F mu q out N seed)‖ ≤ eps} =
      {seed | ‖gradient F (outputOnFunction baseDimension N (sourceQuery mu q) (sourceOutput mu q out N) F seed)‖ ≤ eps} := by
  ext seed
  simp only [Set.mem_setOf_eq]
  rw [actual_value_equals_F F mu hmu,
    actual_source_output_is_same_unqueried_point F hF mu q out baseDimension N seed]


theorem actual_success_probability_is_the_same_source_probability
    [MeasurableSpace Seed] (seeds : Measure Seed) (F : E → ℝ) (hF : ContDiff ℝ 2 F)
    (mu eps : ℝ) (hmu : 0 ≤ mu) (q : Query Seed (SaddleResponse E) (Joint E))
    (out : Seed → State (SaddleResponse E) → E) (baseDimension N : ℕ) :
    seeds {seed | ‖gradient (value F mu) (saddleOutput F mu q out N seed)‖ ≤ eps} =
      seeds {seed | ‖gradient F (outputOnFunction baseDimension N (sourceQuery mu q) (sourceOutput mu q out N) F seed)‖ ≤ eps} :=
  congrArg seeds (actual_success_event_is_the_same_source_event F hF mu eps hmu q out baseDimension N)

section CompleteAlgorithm
variable [FiniteDimensional ℝ E] [MeasurableSpace Seed] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (Joint E)] [BorelSpace (Joint E)]
  [MeasurableSpace (SaddleResponse E)] [BorelSpace (SaddleResponse E)]
  [MeasurableSpace (AllDerivativeResponse E)] [BorelSpace (AllDerivativeResponse E)]

/-- Actual full-O2 reduction has exactly N requests and no F(0) initialization call. -/
theorem actual_decoupled_borel_lift_algorithm_reduction (seeds : Measure Seed)
    (F : E → ℝ) (hF : ContDiff ℝ ∞ F) (mu eps : ℝ) (hmu : 0 ≤ mu)
    (q : Query Seed (SaddleResponse E) (Joint E))
    (hq : ∀ t, Measurable (fun x : Seed × State (SaddleResponse E) => q t x.1 x.2))
    (out : Seed → State (SaddleResponse E) → E)
    (hout : Measurable (fun x : Seed × State (SaddleResponse E) => out x.1 x.2))
    (baseDimension N : ℕ) :
    (∀ t, Measurable (fun x : Seed × State (AllDerivativeResponse E) => sourceQuery mu q t x.1 x.2)) ∧
      Measurable (fun x : Seed × State (AllDerivativeResponse E) => sourceOutput mu q out N x.1 x.2) ∧
      Measurable (actualSaddleRun F mu q N) ∧
      (∀ seed, decodedState mu q N seed (actualBaseRun F mu q baseDimension N seed).2 = actualSaddleRun F mu q N seed) ∧
      (∀ seed, outputOnFunction baseDimension N (sourceQuery mu q) (sourceOutput mu q out N) F seed = saddleOutput F mu q out N seed) ∧
      (∀ seed, actualQueryTrace baseDimension (fun _ : Fin (baseDimension + 1) → E => F) (sourceQuery mu q) N seed 0 =
        (actualSaddleQueryTrace F mu q N seed).map (fun z => z.fst)) ∧
      (∀ seed, (actualQueryTrace baseDimension (fun _ : Fin (baseDimension + 1) → E => F) (sourceQuery mu q) N seed 0).length = N) ∧
      seeds {seed | ‖gradient (value F mu) (saddleOutput F mu q out N seed)‖ ≤ eps} =
        seeds {seed | ‖gradient F (outputOnFunction baseDimension N (sourceQuery mu q) (sourceOutput mu q out N) F seed)‖ ≤ eps} := by
  have h2 : ContDiff ℝ 2 F := hF.of_le (by decide)
  exact ⟨source_query_measurable mu q hq, source_output_measurable mu q hq out hout N,
    actual_saddle_history_measurable F hF mu q hq baseDimension N,
    actual_decoded_history_is_single_fixed_decoupled_history F h2 mu q baseDimension N,
    actual_source_output_is_same_unqueried_point F h2 mu q out baseDimension N,
    actual_source_query_trace_has_no_initialization_request F h2 mu q baseDimension N,
    actual_paid_query_count_is_exactly_N F mu q baseDimension N,
    actual_success_probability_is_the_same_source_probability seeds F h2 mu eps hmu q out baseDimension N⟩

end CompleteAlgorithm

end
end FangqingDecoupledLowerLiftExecution
end

section
-- Source component: FixedHorizonSourceMachine.lean

open MeasureTheory

namespace FangqingFixedHorizonSourceMachine

open OriginalPrefixOracleReplay FangqingSingleLowerEarlyStopPadding
  FangqingSingleLowerAllDerivativeOracle FangqingSingleLowerActualOracleProgram
  FangqingSingleLowerOracleRescaling FangqingSingleLowerFixedFunctionExecution

noncomputable section
set_option maxHeartbeats 6000000

variable {Seed A E : Type*}

abbrev StoredState (Seed A : Type*) := Seed × ℕ × (ℕ → A)

def CounterBlindQuery (q : Query Seed A E) : Prop :=
  ∀ t seed k h, q t seed (k, h) = q t seed (0, h)

def CounterBlindOutput (out : Seed → State A → E) : Prop :=
  ∀ seed k h, out seed (k, h) = out seed (0, h)

def horizonMachine [Zero A] (K : ℕ) (q : Query Seed A E)
    (out : Seed → State A → E) : Machine Seed (StoredState Seed A) E A where
  init seed := (seed, 0, 0)
  stop st := decide (K ≤ st.2.1)
  query st := q st.2.1 st.1 (0, st.2.2)
  update p := (p.1.1, p.1.2.1 + 1, Function.update p.1.2.2 p.1.2.1 p.2)
  output st := out st.1 (0, st.2.2)

section Measurable
variable [Zero A] [MeasurableSpace Seed] [MeasurableSpace A] [MeasurableSpace E]

theorem horizon_machine_is_borel (K : ℕ) (q : Query Seed A E)
    (hq : ∀ t, Measurable (fun x : Seed × State A => q t x.1 x.2))
    (out : Seed → State A → E)
    (hout : Measurable (fun x : Seed × State A => out x.1 x.2)) :
    BorelMachine (horizonMachine K q out) := by
  classical
  constructor
  · exact measurable_id.prodMk (measurable_const.prodMk measurable_const)
  · exact (measurable_of_countable (fun t : ℕ => decide (K ≤ t))).comp
      (measurable_fst.comp measurable_snd)
  · have hQ : Measurable (fun p : ℕ × (Seed × State A) => q p.1 p.2.1 p.2.2) :=
      measurable_from_prod_countable_right hq
    exact hQ.comp ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.prodMk (measurable_const.prodMk (measurable_snd.comp measurable_snd))))
  · have hc : Measurable (fun p : StoredState Seed A × A => p.1.2.1) :=
      measurable_fst.comp (measurable_snd.comp measurable_fst)
    have hs : Measurable (fun p : StoredState Seed A × A => p.1.1) := measurable_fst.comp measurable_fst
    have hh : Measurable (fun p : StoredState Seed A × A => p.1.2.2) :=
      measurable_snd.comp (measurable_snd.comp measurable_fst)
    apply hs.prodMk ((hc.add_const 1).prodMk ?_)
    apply measurable_pi_lambda
    intro i
    have he : MeasurableSet {p : StoredState Seed A × A | i = p.1.2.1} :=
      measurableSet_eq_fun measurable_const hc
    convert! (Measurable.ite he measurable_snd ((measurable_pi_apply i).comp hh)) using 1
    funext p
    simp only [Function.update_apply, Function.comp_def]
    all_goals exact fun _ => Classical.propDecidable _
  · exact hout.comp (measurable_fst.prodMk (measurable_const.prodMk (measurable_snd.comp measurable_snd)))

end Measurable

section ActualSource
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem actual_machine_state_equals_full_source_history
    (K : ℕ) (q : Query Seed (AllDerivativeResponse E) E)
    (out : Seed → State (AllDerivativeResponse E) → E) (hblind : CounterBlindQuery q)
    (F : E → ℝ) (baseDimension N : ℕ) (hN : N ≤ K) (seed : Seed) :
    earlyRun (horizonMachine K q out) (allDerivativeOracle F) N seed =
      (seed, N, (run q (grantEveryResponse baseDimension)
        (familyReply (fun _ : Fin (baseDimension + 1) → E => F)) N seed 0).2) := by
  induction N with
  | zero => rfl
  | succ N ih =>
      have hi := ih (by omega)
      rw [earlyRun, hi]
      have hn : ¬K ≤ N := by omega
      simp only [horizonMachine, hn, decide_false, Bool.false_eq_true, if_false]
      let st := run q (grantEveryResponse baseDimension)
        (familyReply (fun _ : Fin (baseDimension + 1) → E => F)) N seed 0
      change (seed, N + 1, Function.update st.2 N (allDerivativeOracle F (q N seed (0, st.2)))) =
        (seed, N + 1, Function.update st.2 N (allDerivativeOracle F (q N seed st)))
      have hh : q N seed st = q N seed (0, st.2) := hblind N seed st.1 st.2
      rw [hh]

theorem actual_machine_output_equals_full_source_output
    (K : ℕ) (q : Query Seed (AllDerivativeResponse E) E)
    (out : Seed → State (AllDerivativeResponse E) → E)
    (hblind : CounterBlindQuery q) (houtblind : CounterBlindOutput out)
    (F : E → ℝ) (baseDimension : ℕ) (seed : Seed) :
    (horizonMachine K q out).output (earlyRun (horizonMachine K q out) (allDerivativeOracle F) K seed) =
      outputOnFunction baseDimension K q out F seed := by
  rw [actual_machine_state_equals_full_source_history K q out hblind F baseDimension K le_rfl seed]
  symm
  exact houtblind seed _ _

theorem actual_machine_stops_at_its_worst_case_horizon
    (K : ℕ) (q : Query Seed (AllDerivativeResponse E) E)
    (out : Seed → State (AllDerivativeResponse E) → E) (hblind : CounterBlindQuery q)
    (F : E → ℝ) (baseDimension : ℕ) (seed : Seed) :
    (horizonMachine K q out).stop (earlyRun (horizonMachine K q out) (allDerivativeOracle F) K seed) = true := by
  rw [actual_machine_state_equals_full_source_history K q out hblind F baseDimension K le_rfl seed]
  simp only [horizonMachine, le_refl, decide_true]

end ActualSource
end
end FangqingFixedHorizonSourceMachine
end

section
-- Source component: BaselineSaddleInterface.lean

open MeasureTheory
open scoped ContDiff

namespace FangqingBaselineSaddleInterface

open OriginalPrefixOracleReplay FangqingLiftOracleJetBridge JointSliceRegularity

noncomputable section
set_option maxHeartbeats 6000000

variable {Seed E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def bundle (J : Joint E → ℝ) (z : Joint E) : SaddleResponse E :=
  (J z, gradient J z, fderiv ℝ (gradient J) z)

def run (J : Joint E → ℝ) (q : Query Seed (SaddleResponse E) (Joint E)) :
    ℕ → Seed → State (SaddleResponse E)
  | 0, _ => (0, 0)
  | N + 1, seed =>
      let st := run J q N seed
      (N + 1, Function.update st.2 N (bundle J (q N seed st)))

def output (J : Joint E → ℝ) (q : Query Seed (SaddleResponse E) (Joint E))
    (out : Seed → State (SaddleResponse E) → E) (N : ℕ) (seed : Seed) : E :=
  out seed (run J q N seed)

def value (J : Joint E → ℝ) (x : E) : ℝ := sSup (Set.range (fun y => J (point x y)))

structure Valid (J : Joint E → ℝ) (L mu rho Delta : ℝ) : Prop where
  C2 : ContDiff ℝ 2 J
  strongConcavity : ∀ x, StrongConcaveOn (Set.univ : Set E) mu (fun y => J (point x y))
  gradientLip : ∀ z w, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖
  hessianNorm : ∀ z, ‖fderiv ℝ (gradient J) z‖ ≤ L
  hessianLip : ∀ z w, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖
  valueDiff : Differentiable ℝ (value J)
  gap : value J 0 - sInf (Set.range (value J)) ≤ Delta
  exactInitialMaximum : ∀ y, J (point 0 y) ≤ J (point 0 0)
  uniqueInitialMaximum : ∀ y, (∀ z, J (point 0 z) ≤ J (point 0 y)) → y = 0

theorem value_of_large_lift (F : E → ℝ) (mu b : ℝ) (c : E) :
    value (AllDerivativeLift.jointLift F mu b c) = AllDerivativeLift.phi F mu b c := by
  funext x
  apply congrArg sSup
  apply congrArg Set.range
  funext y
  exact AllDerivativeLift.jointLift_eq_lift F mu b c x y

theorem value_of_decoupled_lift (F : E → ℝ) (mu : ℝ) :
    value (FangqingDecoupledLowerLift.objective F mu) = FangqingDecoupledLowerLift.value F mu := by
  funext x
  apply congrArg sSup
  apply congrArg Set.range
  funext y
  exact FangqingDecoupledLowerLift.objective_is_slice F mu x y

theorem run_of_large_lift (F : E → ℝ) (mu b : ℝ)
    (q : Query Seed (SaddleResponse E) (Joint E)) (N : ℕ) (seed : Seed) :
    run (AllDerivativeLift.jointLift F mu b (AllDerivativeLift.initialShift F mu)) q N seed =
      FangqingAllDerivativeLiftExecution.actualSaddleRun F mu b q N seed := by
  induction N with
  | zero => rfl
  | succ N ih => rw [run, FangqingAllDerivativeLiftExecution.actualSaddleRun, ih]; rfl

theorem run_of_decoupled_lift (F : E → ℝ) (mu : ℝ)
    (q : Query Seed (SaddleResponse E) (Joint E)) (N : ℕ) (seed : Seed) :
    run (FangqingDecoupledLowerLift.objective F mu) q N seed =
      FangqingDecoupledLowerLiftExecution.actualSaddleRun F mu q N seed := by
  induction N with
  | zero => rfl
  | succ N ih => rw [run, FangqingDecoupledLowerLiftExecution.actualSaddleRun, ih]; rfl

theorem output_of_large_lift (F : E → ℝ) (mu b : ℝ)
    (q : Query Seed (SaddleResponse E) (Joint E)) (out : Seed → State (SaddleResponse E) → E)
    (N : ℕ) (seed : Seed) :
    output (AllDerivativeLift.jointLift F mu b (AllDerivativeLift.initialShift F mu)) q out N seed =
      FangqingAllDerivativeLiftExecution.saddleOutput F mu b q out N seed := by
  unfold output
  rw [run_of_large_lift]
  rfl

theorem output_of_decoupled_lift (F : E → ℝ) (mu : ℝ)
    (q : Query Seed (SaddleResponse E) (Joint E)) (out : Seed → State (SaddleResponse E) → E)
    (N : ℕ) (seed : Seed) :
    output (FangqingDecoupledLowerLift.objective F mu) q out N seed =
      FangqingDecoupledLowerLiftExecution.saddleOutput F mu q out N seed := by
  unfold output
  rw [run_of_decoupled_lift]
  rfl

section Class
variable [FiniteDimensional ℝ E]

theorem large_lift_is_actually_valid (F : E → ℝ) (hF : ContDiff ℝ 2 F)
    (L mu kappa rho Delta : ℝ) (hmu : 0 < mu) (hk : 6 ≤ kappa) (hL : mu * kappa = L)
    (hrho : 0 < rho) (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ mu)
    (hHLip : ∀ x y, ‖fderiv ℝ (fderiv ℝ F) x - fderiv ℝ (fderiv ℝ F) y‖ ≤ rho * ‖x - y‖)
    (hgap : F 0 - sInf (Set.range F) ≤ Delta) :
    Valid (AllDerivativeLift.jointLift F mu (AllDerivativeLift.scaleB kappa) (AllDerivativeLift.initialShift F mu))
      L mu rho Delta := by
  let b := AllDerivativeLift.scaleB kappa
  let c := AllDerivativeLift.initialShift F mu
  have hnorm : ∀ x, ‖fderiv ℝ (gradient F) x‖ ≤ mu := by
    intro x
    rw [actual_hessian_norm_in_gradient_coordinates F hF x]
    exact hH x
  have hLip : ∀ x y, ‖fderiv ℝ (gradient F) x - fderiv ℝ (gradient F) y‖ ≤ rho * ‖x - y‖ := by
    intro x y
    rw [actual_hessian_difference_norm_in_gradient_coordinates F hF x y]
    exact hHLip x y
  obtain ⟨hJ, hSC, hGL, hHN, hHL, hYunique, hY0, hD, hInf, hGap, hStationarity, hSimulation⟩ :=
    AllDerivativeLift.lift_from_F_class F mu kappa rho Delta hmu hk hrho hF hnorm hLip hgap
  have hd := hF.differentiable (by norm_num)
  have hgradLip := AllDerivativeLift.gradient_lipschitz_from_hessian_norm F hF mu hnorm
  constructor
  · exact hJ
  · intro x
    have heq : (fun y => AllDerivativeLift.jointLift F mu b c (point x y)) = AllDerivativeLift.lift F mu b c x := by
      funext y
      exact AllDerivativeLift.jointLift_eq_lift F mu b c x y
    rw [heq]
    exact hSC x
  · simpa only [hL] using hGL
  · simpa only [hL] using hHN
  · exact hHL
  · rw [value_of_large_lift]
    exact hD
  · rw [value_of_large_lift]
    exact hGap
  · intro y
    have hh := AllDerivativeLift.yStar_maximizes F mu b c hmu hd hgradLip 0 y
    rw [hY0] at hh
    simpa only [AllDerivativeLift.jointLift_eq_lift] using hh
  · intro y hy
    have hh : ∀ z, AllDerivativeLift.lift F mu b c 0 z ≤ AllDerivativeLift.lift F mu b c 0 y := by
      intro z
      simpa only [AllDerivativeLift.jointLift_eq_lift] using hy z
    have heq := AllDerivativeLift.inner_maximum_unique F mu b c hmu hd hgradLip 0 y hh
    rw [hY0] at heq
    exact heq.symm

theorem decoupled_lift_is_actually_valid (F : E → ℝ) (hF : ContDiff ℝ 2 F)
    (L mu rho Delta : ℝ) (hmu : 0 < mu) (hmL : mu ≤ L) (hrho : 0 ≤ rho)
    (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ L)
    (hHLip : ∀ x y, ‖fderiv ℝ (fderiv ℝ F) x - fderiv ℝ (fderiv ℝ F) y‖ ≤ rho * ‖x - y‖)
    (hgap : F 0 - sInf (Set.range F) ≤ Delta) :
    Valid (FangqingDecoupledLowerLift.objective F mu) L mu rho Delta := by
  obtain ⟨hJ, hSC, hGL, hHN, hHL, hMax, hValue, hGap⟩ :=
    FangqingDecoupledLowerLift.actual_class_and_exact_normalization F hF mu L rho Delta hmu hmL hrho hH hHLip hgap
  constructor
  · exact hJ
  · intro x
    have heq : (fun y => FangqingDecoupledLowerLift.objective F mu (point x y)) = FangqingDecoupledLowerLift.slice F mu x := by
      funext y
      exact FangqingDecoupledLowerLift.objective_is_slice F mu x y
    rw [heq]
    exact hSC x
  · exact hGL
  · exact hHN
  · exact hHL
  · rw [value_of_decoupled_lift, hValue]
    exact hF.differentiable (by norm_num)
  · rw [value_of_decoupled_lift]
    exact hGap
  · intro y
    simpa only [FangqingDecoupledLowerLift.objective_is_slice] using (hMax 0).1 y
  · intro y hy
    apply (hMax 0).2 y
    intro z
    simpa only [FangqingDecoupledLowerLift.objective_is_slice] using hy z

end Class
end
end FangqingBaselineSaddleInterface
end

section
-- Source component: BaselineRateScalars.lean

open scoped ContDiff

namespace FangqingBaselineRateScalars

open FangqingActualRelayScaling FangqingSingleLowerNormalizationScalars

noncomputable section
set_option maxHeartbeats 6000000

def rhoAt (L kappa eps r : ℝ) : ℝ := r * L ^ 2 / (kappa * Real.sqrt kappa * eps)
def mass (L eps Delta r : ℝ) : ℝ := Delta / energy L eps * min 1 (Real.sqrt r)
def sourceRate (c ell rho delta Delta : ℝ) : ℝ :=
  c * Delta * min (ell * delta ^ (-2 : ℝ)) (Real.sqrt rho * delta ^ (-(3 / 2 : ℝ)))

theorem source_rate_division_form (c ell rho delta Delta : ℝ) (hrho : 0 ≤ rho) (hd : 0 < delta) :
    sourceRate c ell rho delta Delta = c * Delta * min (ell / delta ^ 2) (Real.sqrt (rho / delta ^ 3)) := by
  rw [sourceRate, exact_original_two_smoothness_rate ell rho delta hrho hd]

theorem large_kappa_rate_terms (L mu kappa eps r : ℝ) (hL : 0 < L) (hmu : 0 < mu)
    (heps : 0 < eps) (hr : 0 < r) (hk : 6 ≤ kappa) (hrel : mu * kappa = L) :
    let b := AllDerivativeLift.scaleB kappa
    let delta := 3 * eps / (2 * b)
    L / (9 * eps ^ 2) ≤ mu / delta ^ 2 ∧
      L / (9 * eps ^ 2) * Real.sqrt r ≤ Real.sqrt (rhoAt L kappa eps r / delta ^ 3) := by
  intro b delta
  have hkpos : 0 < kappa := by linarith
  have hspos : 0 < Real.sqrt kappa := Real.sqrt_pos.mpr hkpos
  have hs := Real.sq_sqrt hkpos.le
  have hp := AllDerivativeLift.scaleB_properties kappa hk
  have hb : 0 < b := hp.1
  have hbsq : b ^ 2 = (kappa - 3) / 2 := hp.2.1
  have hd : 0 < delta := by dsimp [delta]; positivity
  have h2b : Real.sqrt kappa ≤ 2 * b := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg kappa) (by positivity : 0 ≤ 2 * b)).mp
    nlinarith only [hs, hbsq, hk]
  have hcube := pow_le_pow_left₀ (Real.sqrt_nonneg kappa) h2b 3
  have hkscube : Real.sqrt kappa ^ 3 = kappa * Real.sqrt kappa := by
    calc
      _ = Real.sqrt kappa ^ 2 * Real.sqrt kappa := by ring
      _ = _ := by rw [hs]
  have hcoef : kappa * Real.sqrt kappa ≤ 8 * b ^ 3 := by
    nlinarith only [hcube, hkscube]
  constructor
  · have heq : mu / delta ^ 2 = 4 * mu * b ^ 2 / (9 * eps ^ 2) := by
      dsimp [delta]
      field_simp [hb.ne', heps.ne']
      <;> ring
    rw [heq]
    apply (div_le_div_iff_of_pos_right (by positivity : 0 < 9 * eps ^ 2)).mpr
    have hh := mul_le_mul_of_nonneg_left (show kappa ≤ 4 * b ^ 2 by nlinarith only [hbsq, hk]) hmu.le
    nlinarith only [hh, hrel]
  · let P := r * L ^ 2 / eps ^ 4
    have hleft : (L / (9 * eps ^ 2) * Real.sqrt r) ^ 2 = P / 81 := by
      dsimp [P]
      rw [mul_pow, Real.sq_sqrt hr.le]
      field_simp [heps.ne']
      <;> ring
    have hright : rhoAt L kappa eps r / delta ^ 3 = P * (8 * b ^ 3 / (27 * kappa * Real.sqrt kappa)) := by
      dsimp [rhoAt, delta, P]
      field_simp [hb.ne', heps.ne', hkpos.ne', hspos.ne']
      <;> ring
    have hcoeff : (1 / 81 : ℝ) ≤ 8 * b ^ 3 / (27 * kappa * Real.sqrt kappa) := by
      apply (le_div_iff₀ (by positivity : 0 < 27 * kappa * Real.sqrt kappa)).mpr
      have hh : 0 ≤ kappa * Real.sqrt kappa := by positivity
      nlinarith only [hcoef, hh]
    apply Real.le_sqrt_of_sq_le
    rw [hleft, hright]
    simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hcoeff (by dsimp [P]; positivity : 0 ≤ P)

theorem small_kappa_rate_terms (L kappa eps r : ℝ) (hL : 0 < L) (heps : 0 < eps)
    (hr : 0 < r) (hkpos : 0 < kappa) (hk : kappa < 6) :
    L / (9 * eps ^ 2) ≤ L / eps ^ 2 ∧
      L / (9 * eps ^ 2) * Real.sqrt r ≤ Real.sqrt (rhoAt L kappa eps r / eps ^ 3) := by
  constructor
  · apply (div_le_div_iff₀ (by positivity : 0 < 9 * eps ^ 2) (by positivity : 0 < eps ^ 2)).mpr
    nlinarith [sq_pos_of_pos heps]
  · have hspos : 0 < Real.sqrt kappa := Real.sqrt_pos.mpr hkpos
    have hs : Real.sqrt kappa ≤ 6 := (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 6)).mpr (by nlinarith)
    have hks : kappa * Real.sqrt kappa ≤ 36 := by
      have hh := mul_le_mul hk.le hs (Real.sqrt_nonneg kappa) (by norm_num : (0 : ℝ) ≤ 6)
      norm_num at hh ⊢
      exact hh
    let P := r * L ^ 2 / eps ^ 4
    have hleft : (L / (9 * eps ^ 2) * Real.sqrt r) ^ 2 = P / 81 := by
      dsimp [P]
      rw [mul_pow, Real.sq_sqrt hr.le]
      field_simp [heps.ne']
      <;> ring
    have hright : rhoAt L kappa eps r / eps ^ 3 = P * (1 / (kappa * Real.sqrt kappa)) := by
      dsimp [rhoAt, P]
      field_simp [heps.ne', hkpos.ne', hspos.ne']
      <;> ring
    have hcoeff : (1 / 81 : ℝ) ≤ 1 / (kappa * Real.sqrt kappa) := by
      apply (le_div_iff₀ (by positivity : 0 < kappa * Real.sqrt kappa)).mpr
      nlinarith only [hks]
    apply Real.le_sqrt_of_sq_le
    rw [hleft, hright]
    simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hcoeff (by dsimp [P]; positivity : 0 ≤ P)

theorem rate_dominates_baseline_mass (c ell rho delta L eps Delta r : ℝ)
    (hc : 0 < c) (hL : 0 < L) (heps : 0 < eps) (hDelta : 0 < Delta)
    (hrho : 0 ≤ rho) (hdelta : 0 < delta)
    (hfirst : L / (9 * eps ^ 2) ≤ ell / delta ^ 2)
    (hsecond : L / (9 * eps ^ 2) * Real.sqrt r ≤ Real.sqrt (rho / delta ^ 3)) :
    (c / 9) * mass L eps Delta r ≤ sourceRate c ell rho delta Delta := by
  rw [source_rate_division_form c ell rho delta Delta hrho hdelta]
  have hbase : 0 ≤ L / (9 * eps ^ 2) := by positivity
  have hm : L / (9 * eps ^ 2) * min 1 (Real.sqrt r) ≤ min (ell / delta ^ 2) (Real.sqrt (rho / delta ^ 3)) := by
    apply le_min
    · calc
        _ ≤ L / (9 * eps ^ 2) * 1 := mul_le_mul_of_nonneg_left (min_le_left 1 (Real.sqrt r)) hbase
        _ ≤ ell / delta ^ 2 := by simpa only [mul_one] using hfirst
    · exact (mul_le_mul_of_nonneg_left (min_le_right 1 (Real.sqrt r)) hbase).trans hsecond
  have hh := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ c * Delta)
  convert! hh using 1
  dsimp [mass, energy]
  field_simp [heps.ne', hL.ne']
  <;> ring

theorem bootstrap_query_is_absorbed (T B : ℝ) (N : ℕ) (hT : 2 ≤ T) (hBT : 2 * B ≤ T)
    (hN : (N : ℝ) < B) : ((N + 1 : ℕ) : ℝ) < T := by
  by_cases hz : N = 0
  · subst N
    norm_num at hN ⊢
    linarith
  · have hOne : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    push_cast
    nlinarith

theorem subthreshold_budget_is_zero (T B : ℝ) (N : ℕ) (hT : T < 2) (hBT : 2 * B ≤ T)
    (hN : (N : ℝ) < B) : N = 0 := by
  have hsmall : (N : ℝ) < 1 := by linarith
  have hn : N < 1 := by exact_mod_cast hsmall
  omega

end
end FangqingBaselineRateScalars
end

section
-- Source component: ZeroQueryQuadraticLower.lean

open MeasureTheory Function
open scoped ContDiff BigOperators

namespace FangqingZeroQueryQuadraticLower
noncomputable section
set_option maxHeartbeats 4500000

variable {E Seed : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def quadratic (L : ℝ) (a : E) (x : E) : ℝ := (L/2)*‖x-a‖^2

theorem smooth (L : ℝ) (a : E) : ContDiff ℝ ∞ (quadratic L a) :=
  contDiff_const.mul ((contDiff_id.sub contDiff_const).norm_sq ℝ)

theorem actual_fderiv (L : ℝ) (a x : E) :
    fderiv ℝ (quadratic L a) x = L • innerSL ℝ (x-a) := by
  have h := (((hasFDerivAt_id x).sub_const a).norm_sq).const_mul (L/2)
  change fderiv ℝ (fun y => (L/2)*‖y-a‖^2) x = _
  convert! h.fderiv using 1
  ext v
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply, smul_eq_mul,id_eq]
  ring

theorem actual_hessian (L : ℝ) (a x : E) :
    fderiv ℝ (fderiv ℝ (quadratic L a)) x = L • (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) := by
  have he : fderiv ℝ (quadratic L a) = fun y => L • innerSL ℝ (y-a) := funext (actual_fderiv L a)
  rw [he]
  exact (((innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).hasFDerivAt.comp x
    ((hasFDerivAt_id x).sub_const a)).const_smul L).fderiv

theorem hessian_norm (L : ℝ) (hL : 0 ≤ L) (a x : E) :
    ‖fderiv ℝ (fderiv ℝ (quadratic L a)) x‖ ≤ L := by
  rw [actual_hessian]
  apply ContinuousLinearMap.opNorm_le_bound _ hL
  intro v
  change ‖L • innerSL ℝ v‖ ≤ L*‖v‖
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hL,innerSL_apply_norm]

theorem hessian_lipschitz (L rho : ℝ) (hrho : 0 ≤ rho) (a x y : E) :
    ‖fderiv ℝ (fderiv ℝ (quadratic L a)) x - fderiv ℝ (fderiv ℝ (quadratic L a)) y‖ ≤ rho*‖x-y‖ := by
  simp only [actual_hessian,sub_self]
  have hz : ‖(0 : E →L[ℝ] E →L[ℝ] ℝ)‖ = 0 := ContinuousLinearMap.opNorm_zero
  rw [hz]
  positivity

theorem minimum_is_zero (L : ℝ) (hL : 0 ≤ L) (a : E) :
    BddBelow (Set.range (quadratic L a)) ∧ sInf (Set.range (quadratic L a)) = 0 := by
  have hnonneg : ∀ x, 0 ≤ quadratic L a x := by intro x; unfold quadratic; positivity
  have hb : BddBelow (Set.range (quadratic L a)) := ⟨0,by rintro _ ⟨x,rfl⟩; exact hnonneg x⟩
  refine ⟨hb,le_antisymm ?_ (le_csInf (Set.range_nonempty _) (by rintro _ ⟨x,rfl⟩; exact hnonneg x))⟩
  have h := csInf_le hb (Set.mem_range_self a : quadratic L a a ∈ Set.range (quadratic L a))
  simpa only [quadratic,sub_self,norm_zero,zero_pow (by norm_num : 2≠0),mul_zero] using h

section Complete
variable [CompleteSpace E]

theorem actual_gradient (L : ℝ) (a x : E) : gradient (quadratic L a) x = L • (x-a) := by
  have hg : HasGradientAt (quadratic L a) (L • (x-a)) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert! ((smooth L a).differentiable (by norm_num) x).hasFDerivAt using 1
    rw [actual_fderiv]
    ext v
    simp only [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.smul_apply,
      innerSL_apply_apply, real_inner_smul_left,smul_eq_mul]
  exact hg.gradient

def center (L eps : ℝ) (v : E) (i : Fin 3) : E :=
  (((i.val:ℝ)-1)*(3*eps/L)) • v

theorem center_norm_bound (L eps : ℝ) (hL : 0 < L) (heps : 0 < eps)
    (v : E) (hv : ‖v‖=1) (i : Fin 3) : ‖center L eps v i‖ ≤ 3*eps/L := by
  rw [center,norm_smul,hv,mul_one,Real.norm_eq_abs,abs_mul,abs_of_pos (by positivity : 0 < 3*eps/L)]
  have hi : |(i.val:ℝ)-1| ≤ 1 := by
    have hi0 : (0:ℝ) ≤ i.val := by positivity
    have hi2 : (i.val:ℝ) ≤ 2 := by exact_mod_cast (show i.val ≤ 2 by omega)
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hi (by positivity : 0 ≤ 3*eps/L)

theorem family_gap (L eps Delta : ℝ) (hL : 0 < L) (heps : 0 < eps)
    (hGap : 5*eps^2 ≤ Delta*L) (v : E) (hv : ‖v‖=1) (i : Fin 3) :
    quadratic L (center L eps v i) 0 - sInf (Set.range (quadratic L (center L eps v i))) ≤ Delta := by
  rw [(minimum_is_zero L hL.le _).2,sub_zero]
  have hn := center_norm_bound L eps hL heps v hv i
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 3*eps/L)).mpr hn
  simp only [quadratic,zero_sub,norm_neg]
  apply (mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ L/2)).trans
  have he : L/2*(3*eps/L)^2 = (9*eps^2/2)/L := by field_simp <;> norm_num
  rw [he]
  apply (div_le_iff₀ hL).mpr
  nlinarith only [hGap,sq_nonneg eps]

theorem separated_centers (L eps : ℝ) (hL : 0 < L) (heps : 0 < eps)
    (v : E) (hv : ‖v‖=1) {i j : Fin 3} (hij : i≠j) :
    2*eps < L*‖center L eps v i-center L eps v j‖ := by
  have hd : (1:ℝ) ≤ |(i.val:ℝ)-(j.val:ℝ)| := by
    have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    rcases lt_or_gt_of_ne hne with h | h
    · have hr : (i.val:ℝ) < j.val := by exact_mod_cast h
      rw [abs_of_neg (sub_neg.mpr hr)]
      have hh : i.val+1 ≤ j.val := by omega
      have hh' : (i.val:ℝ)+1 ≤ j.val := by exact_mod_cast hh
      linarith
    · have hr : (j.val:ℝ) < i.val := by exact_mod_cast h
      rw [abs_of_pos (sub_pos.mpr hr)]
      have hh : j.val+1 ≤ i.val := by omega
      have hh' : (j.val:ℝ)+1 ≤ i.val := by exact_mod_cast hh
      linarith
  have he : center L eps v i-center L eps v j =
      (((i.val:ℝ)-(j.val:ℝ))*(3*eps/L)) • v := by
    unfold center
    rw [← sub_smul]
    congr 1
    ring
  rw [he,norm_smul,hv,mul_one,Real.norm_eq_abs,abs_mul,abs_of_pos (by positivity : 0 < 3*eps/L)]
  have hh := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 3*eps)
  have heq : L*(|(i.val:ℝ)-(j.val:ℝ)| * (3*eps/L)) = 3*eps * |(i.val:ℝ)-(j.val:ℝ)| := by field_simp <;> norm_num
  rw [heq]
  linarith only [hh,heps]

theorem success_sets_disjoint (L eps : ℝ) (hL : 0 < L) (heps : 0 < eps)
    (v : E) (hv : ‖v‖=1) (out0 : Seed → E) :
    Pairwise (Disjoint on (fun i : Fin 3 => {s | ‖gradient (quadratic L (center L eps v i)) (out0 s)‖ ≤ eps})) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro s hi hj
  simp only [Set.mem_setOf_eq,actual_gradient,norm_smul,Real.norm_eq_abs,abs_of_pos hL] at hi hj
  have ht := norm_sub_le_norm_sub_add_norm_sub (center L eps v i) (out0 s) (center L eps v j)
  rw [norm_sub_rev (center L eps v i) (out0 s)] at ht
  have hh := mul_le_mul_of_nonneg_left ht hL.le
  have hs := separated_centers L eps hL heps v hv hij
  nlinarith only [hi,hj,hh,hs]

variable [MeasurableSpace Seed] [MeasurableSpace E] [BorelSpace E]

theorem fixed_quadratic_defeats_zero_query_output
    (L eps Delta rho : ℝ) (hL : 0 < L) (heps : 0 < eps) (hrho : 0 ≤ rho)
    (hGap : 5*eps^2 ≤ Delta*L) (v : E) (hv : ‖v‖=1)
    (sigma : Measure Seed) [IsProbabilityMeasure sigma] (out0 : Seed → E) (hout : Measurable out0) :
    ∃ F : E → ℝ,
      ContDiff ℝ ∞ F ∧ BddBelow (Set.range F) ∧
      (∀ x, ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ L) ∧
      (∀ x y, ‖fderiv ℝ (fderiv ℝ F) x-fderiv ℝ (fderiv ℝ F) y‖ ≤ rho*‖x-y‖) ∧
      F 0-sInf (Set.range F) ≤ Delta ∧
      sigma.real {s | ‖gradient F (out0 s)‖ ≤ eps} ≤ 1/3 := by
  let S : Fin 3 → Set Seed := fun i => {s | ‖gradient (quadratic L (center L eps v i)) (out0 s)‖ ≤ eps}
  have hm : ∀ i, MeasurableSet (S i) := by
    intro i
    have hc : Continuous (fun x : E => ‖L • (x-center L eps v i)‖) := by fun_prop
    simpa only [S,actual_gradient,Function.comp_def] using measurableSet_le (hc.measurable.comp hout) measurable_const
  have hd : Pairwise (Disjoint on S) := success_sets_disjoint L eps hL heps v hv out0
  have hs : (∑ i : Fin 3, sigma.real (S i)) ≤ 1 := by
    rw [← measureReal_iUnion_fintype hd hm]
    exact measureReal_le_one
  have hex : ∃ i : Fin 3, sigma.real (S i) ≤ 1/3 := by
    by_contra hn
    have h0 : 1/3 < sigma.real (S 0) := lt_of_not_ge (fun h => hn ⟨0,h⟩)
    have h1 : 1/3 < sigma.real (S 1) := lt_of_not_ge (fun h => hn ⟨1,h⟩)
    have h2 : 1/3 < sigma.real (S 2) := lt_of_not_ge (fun h => hn ⟨2,h⟩)
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Fin.succ_zero_eq_one,Fin.succ_one_eq_two] at hs
    norm_num at hs
    linarith
  obtain ⟨i,hi⟩ := hex
  exact ⟨quadratic L (center L eps v i),smooth L _,(minimum_is_zero L hL.le _).1,
    hessian_norm L hL.le _,hessian_lipschitz L rho hrho _,family_gap L eps Delta hL heps hGap v hv i,hi⟩

end Complete
end
end FangqingZeroQueryQuadraticLower
end

section
-- Source component: SingleLowerFiniteInfMinimax.lean

section

open MeasureTheory
open scoped ContDiff ENNReal

namespace FangqingSingleLowerOriginalFiniteInf

open FangqingSingleLowerNormalizedLower FangqingSingleLowerNormalizationScalars
  FangqingSingleLowerDimensionBudget FangqingSingleLowerOriginalParameters
  FangqingSingleLowerPhysicalGradient FangqingSingleLowerLocalizedGap
  FangqingSingleLowerAllDerivativeOracle FangqingSingleLowerActualOracleProgram
  FangqingSingleLowerFixedHaarWorld FangqingSingleLowerOracleRescaling
  FangqingSingleLowerFixedFunctionExecution OriginalPrefixOracleReplay
  FangqingAdaptiveHaarProduct FangqingAdaptiveHaarConcrete

noncomputable section

universe v

theorem gradient_norm_is_derivative_norm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : E → ℝ) (x : E) :
    ‖gradient f x‖ = ‖fderiv ℝ f x‖ :=
  (InnerProductSpace.toDual ℝ E).symm.norm_map _

/-- The original worst-case oracle convention: one fixed legal function is
    selected against each measurable randomized algorithm, independently of its seed. -/
theorem original_contextual_minimax_all_derivative_lower :
    ∃ c Cdim : ℝ, 0 < c ∧ 0 < Cdim ∧
      ∀ ell rho delta Delta : ℝ, 0 < ell → 0 < rho → 0 < delta → 0 < Delta →
      let T := c * Delta *
        min (ell * delta ^ (-2 : ℝ)) (Real.sqrt rho * delta ^ (-(3 / 2 : ℝ)))
      2 ≤ T → ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ Cdim * T ^ 2 * Real.log T ∧
      ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
        [MeasurableSpace (Response E)] [BorelSpace (Response E)],
      ∀ (b : OrthonormalBasis (Fin d) ℝ E),
      ∀ (Seed : Type v) [MeasurableSpace Seed] (seeds : Measure Seed) [IsProbabilityMeasure seeds],
      ∀ N : ℕ, (N : ℝ) < T → ∀ (q : Query Seed (Response E) E),
        (∀ t, Measurable (fun x : Seed × State (Response E) => q t x.1 x.2)) →
      ∀ (out : Seed → State (Response E) → E),
        Measurable (fun x : Seed × State (Response E) => out x.1 x.2) →
      ∃ f : E → ℝ, ContDiff ℝ ∞ f ∧ BddBelow (Set.range f) ∧ f 0 - sInf (Set.range f) ≤ Delta ∧
        (∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ ell) ∧
        (∀ x y, ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤ rho * ‖x - y‖) ∧
        (2 / 3 : ℝ≥0∞) ≤ seeds {seed | delta <
          ‖gradient f (outputOnFunction (Nat.ceil T) N q out f seed)‖} := by
  obtain ⟨CR, C2, C3, hCR, hC2, hC3, hnormalized⟩ :=
    actual_universal_normalized_all_derivative_lower_family.{0, v}
  let B : ℝ := 4 * Real.pi
  have hB : 1 ≤ B := by dsimp [B]; linarith only [Real.pi_gt_three]
  let c := universalRateConstant B C2 C3
  have hc : 0 < c := (universal_budget_margins B C2 C3 hB (zero_le_one.trans hC2)
    (zero_le_one.trans hC3)).1
  refine ⟨c, 300000 * (CR ^ 2 + 1), hc, by positivity, ?_⟩
  intro ell rho delta Delta hell hrho hdelta hDelta T hT
  let n := Nat.ceil T
  let m := n + 1
  let d := dimension CR m
  let alpha : ℝ := Delta / (B * m)
  let beta : ℝ := alpha / (4 * delta)
  let R := CR * Real.sqrt m
  have hp := actual_original_rounded_parameters B C2 C3 CR ell rho delta Delta hB
    (zero_le_one.trans hC2) (zero_le_one.trans hC3) (zero_lt_one.trans_le hCR)
    hell hrho hdelta hDelta hT
  have hT_eq : originalT B C2 C3 ell rho delta Delta = T := rfl
  rw [hT_eq] at hp
  rcases hp with ⟨ha, hb, hR, hmd, hAlphaBudget, hratio, hessBudget, thirdBudget, hdim, hNbound⟩
  change 0 < alpha at ha
  change 0 < beta at hb
  change m ≤ d at hmd
  change alpha * B * m = Delta at hAlphaBudget
  have hdp : 0 < d := by
    have hm : 0 < m := by dsimp [m]; omega
    omega
  refine ⟨d, hdp, hdim, ?_⟩
  intro E inst inst' inst'' inst''' instM instB instN instResp instBResp
    b Seed instSeed seeds instProb N hN q hq out hout
  obtain ⟨hn, hHaarBudget⟩ := hNbound N hN
  change N ≤ n at hn
  have hHaarBudget' : 2 * (2 * R) ^ 2 / (1 / 4 : ℝ) ^ 2 *
      Real.log ((2 * 1 * (N + 1) * (n + 1)) / (1 / 6 : ℝ)) ≤ ((d - (n + 1) : ℕ) : ℝ) := by
    simpa only [R, m, Nat.cast_add, Nat.cast_one] using hHaarBudget
  have hqb := baseQuery_measurable alpha beta q hq
  have hob := baseOutput_measurable alpha beta out hout
  obtain ⟨g, hSmooth, hGap, hHess, hHessLip, hProb⟩ :=
    hnormalized E Seed seeds n N d hn b hmd (baseQuery alpha beta q) hqb
      (baseOutput alpha beta out) hob hHaarBudget'
  let family : (Fin (n + 1) → E) → E → ℝ :=
    localizedChain FangqingPublicShellProfiles.theta R n
  let V : Fin (n + 1) → E := frame (basisPrefix b hmd) g
  let f := scaledFunction alpha beta (family V)
  have hFamily : ∀ V, ContDiff ℝ ∞ (family V) :=
    fun V => actual_localized_chain_smooth _ FangqingPublicShellProfiles.theta_smooth R n V
  have hbaseGap : family V 0 - sInf (Set.range (family V)) ≤ B * m := by
    simpa only [family, V, B, R, m, Nat.cast_add, Nat.cast_one] using hGap
  have hGapScale : alpha * (B * m) ≤ Delta := by nlinarith only [hAlphaBudget]
  have hscaled := scaled_actual_class_and_initial_gap alpha beta C2 C3 (B * m) ell rho Delta
    ha hb (family V) hSmooth hHess hHessLip hbaseGap hessBudget thirdBudget
      hGapScale
  have hbaseProb : (2 / 3 : ℝ≥0∞) ≤ seeds {seed | (9 / 10 : ℝ) ≤
      ‖fderiv ℝ (family V) (baseOutput alpha beta out seed
        (run (baseQuery alpha beta q) (grantEveryResponse n) (familyReply family) N seed V))‖} := by
    have hReplyEq : (FangqingSingleLowerActualOracleProgram.reply FangqingPublicShellProfiles.theta R n :
        Reply Seed E (Response E) E (n + 1)) = familyReply family := rfl
    change (2 / 3 : ℝ≥0∞) ≤ seeds {seed | (9 / 10 : ℝ) ≤
      ‖fderiv ℝ (family V) (baseOutput alpha beta out seed
        (run (baseQuery alpha beta q) (grantEveryResponse n)
          (FangqingSingleLowerActualOracleProgram.reply FangqingPublicShellProfiles.theta R n) N seed V))‖} at hProb
    rw [hReplyEq] at hProb
    exact hProb
  have hprob := hbaseProb.trans
    (actual_scaled_program_failure_measure seeds alpha beta delta ha hb hdelta hratio n family hFamily q out N V)
  have hfixed (seed : Seed) : out seed
      (run q (grantEveryResponse n) (familyReply (scaledFamily alpha beta family)) N seed V) =
        outputOnFunction n N q out f seed :=
    actual_output_is_the_output_on_one_fixed_function n N (scaledFamily alpha beta family) q out seed V
  have hbounded : BddBelow (Set.range f) := by
    refine ⟨alpha * (-(4 * Real.pi * (n + 1))), ?_⟩
    rintro z ⟨x, rfl⟩
    exact mul_le_mul_of_nonneg_left
      (actual_localized_chain_global_lower_bound FangqingPublicShellProfiles.theta
        FangqingPublicShellProfiles.theta_range R n V (beta⁻¹ • x)) ha.le
  refine ⟨f, hscaled.1, hbounded, hscaled.2.1, hscaled.2.2.1, hscaled.2.2.2, ?_⟩
  change (2 / 3 : ℝ≥0∞) ≤ seeds {seed | delta < ‖fderiv ℝ f
    (out seed (run q (grantEveryResponse n) (familyReply (scaledFamily alpha beta family)) N seed V))‖} at hprob
  simp_rw [hfixed] at hprob
  simpa only [gradient_norm_is_derivative_norm] using hprob

end
end FangqingSingleLowerOriginalFiniteInf
end


section

open MeasureTheory
open scoped ContDiff ENNReal

namespace FangqingSingleLowerEuclideanFiniteInf

open FangqingSingleLowerOriginalFiniteInf FangqingSingleLowerActualOracleProgram
  FangqingSingleLowerFixedFunctionExecution FangqingSingleLowerAlgorithmMeasurability
  FangqingSingleLowerCanonicalEuclidean OriginalPrefixOracleReplay

noncomputable section

universe v

theorem original_euclidean_all_derivative_minimax_lower :
    ∃ c Cdim : ℝ, 0 < c ∧ 0 < Cdim ∧
      ∀ ell rho delta Delta : ℝ, 0 < ell → 0 < rho → 0 < delta → 0 < Delta →
      let T := c * Delta *
        min (ell * delta ^ (-2 : ℝ)) (Real.sqrt rho * delta ^ (-(3 / 2 : ℝ)))
      2 ≤ T → ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ Cdim * T ^ 2 * Real.log T ∧
      letI : MeasurableSpace (Response (EuclideanSpace ℝ (Fin d))) := canonicalResponseMeasurableSpace d
      ∀ (Seed : Type v) [MeasurableSpace Seed] (seeds : Measure Seed) [IsProbabilityMeasure seeds],
      ∀ N : ℕ, (N : ℝ) < T → ∀ (q : Query Seed (Response (EuclideanSpace ℝ (Fin d))) (EuclideanSpace ℝ (Fin d))),
        (∀ t, Measurable (fun x : Seed × State (Response (EuclideanSpace ℝ (Fin d))) => q t x.1 x.2)) →
      ∀ (out : Seed → State (Response (EuclideanSpace ℝ (Fin d))) → EuclideanSpace ℝ (Fin d)),
        Measurable (fun x : Seed × State (Response (EuclideanSpace ℝ (Fin d))) => out x.1 x.2) →
      ∃ f : EuclideanSpace ℝ (Fin d) → ℝ,
        ContDiff ℝ ∞ f ∧ BddBelow (Set.range f) ∧ f 0 - sInf (Set.range f) ≤ Delta ∧
        (∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ ell) ∧
        (∀ x y, ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤ rho * ‖x - y‖) ∧
        seeds {seed | ‖gradient f (outputOnFunction (Nat.ceil T) N q out f seed)‖ ≤ delta} ≤
          (1 / 3 : ℝ≥0∞) := by
  obtain ⟨c, Cdim, hc, hCdim, hAll⟩ := original_contextual_minimax_all_derivative_lower.{v}
  refine ⟨c, Cdim, hc, hCdim, ?_⟩
  intro ell rho delta Delta hell hrho hdelta hDelta T hT
  obtain ⟨d, hd, hdim, hLower⟩ := hAll ell rho delta Delta hell hrho hdelta hDelta hT
  refine ⟨d, hd, hdim, ?_⟩
  letI : Nontrivial (EuclideanSpace ℝ (Fin d)) := canonical_euclidean_nontrivial d hd
  letI : MeasurableSpace (Response (EuclideanSpace ℝ (Fin d))) := canonicalResponseMeasurableSpace d
  letI : BorelSpace (Response (EuclideanSpace ℝ (Fin d))) := canonical_response_borel d
  intro Seed instSeed seeds instProb N hN q hq out hout
  obtain ⟨f, hf, hbounded, hgap, hHess, hHessLip, hfail⟩ :=
    hLower (EuclideanSpace ℝ (Fin d)) (canonicalBasis d) Seed seeds N hN q hq out hout
  exact ⟨f, hf, hbounded, hgap, hHess, hHessLip,
    actual_failure_probability_bounds_success seeds (Nat.ceil T) N q hq out hout f hf delta hfail⟩

end
end FangqingSingleLowerEuclideanFiniteInf
end


section

open MeasureTheory
open scoped ContDiff ENNReal

namespace FangqingSingleLowerArbitraryFiniteInf

open FangqingSingleLowerEuclideanFiniteInf FangqingSingleLowerActualOracleProgram
  FangqingSingleLowerAllDerivativeOracle FangqingSingleLowerCanonicalEuclidean
  FangqingSingleLowerEarlyStopPadding

noncomputable section

universe v w

/-- Arbitrary measurable state and early stopping are included. A bounded
    algorithm's state is frozen after its actual stop, and the function is
    selected once before drawing its independent random seed. -/
theorem original_arbitrary_measurable_algorithm_minimax_lower :
    ∃ c Cdim : ℝ, 0 < c ∧ 0 < Cdim ∧
      ∀ ell rho delta Delta : ℝ, 0 < ell → 0 < rho → 0 < delta → 0 < Delta →
      let T := c * Delta *
        min (ell * delta ^ (-2 : ℝ)) (Real.sqrt rho * delta ^ (-(3 / 2 : ℝ)))
      2 ≤ T → ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ Cdim * T ^ 2 * Real.log T ∧
      letI : MeasurableSpace (Response (EuclideanSpace ℝ (Fin d))) := canonicalResponseMeasurableSpace d
      ∀ (Seed : Type v) [MeasurableSpace Seed] (seeds : Measure Seed) [IsProbabilityMeasure seeds],
      ∀ (S : Type w) [MeasurableSpace S],
      ∀ (M : Machine Seed S (EuclideanSpace ℝ (Fin d)) (Response (EuclideanSpace ℝ (Fin d)))),
      BorelMachine M → ∀ N : ℕ, (N : ℝ) < T →
      ∃ f : EuclideanSpace ℝ (Fin d) → ℝ,
        ContDiff ℝ ∞ f ∧ BddBelow (Set.range f) ∧ f 0 - sInf (Set.range f) ≤ Delta ∧
        (∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ ell) ∧
        (∀ x y, ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤ rho * ‖x - y‖) ∧
        seeds {seed | ‖gradient f (M.output (earlyRun M (allDerivativeOracle f) N seed))‖ ≤ delta} ≤
          (1 / 3 : ℝ≥0∞) := by
  obtain ⟨c, Cdim, hc, hCdim, hAll⟩ := original_euclidean_all_derivative_minimax_lower.{v}
  refine ⟨c, Cdim, hc, hCdim, ?_⟩
  intro ell rho delta Delta hell hrho hdelta hDelta T hT
  obtain ⟨d, hd, hdim, hLower⟩ := hAll ell rho delta Delta hell hrho hdelta hDelta hT
  refine ⟨d, hd, hdim, ?_⟩
  letI : MeasurableSpace (Response (EuclideanSpace ℝ (Fin d))) := canonicalResponseMeasurableSpace d
  intro Seed instSeed seeds instProb S instS M hM N hN
  obtain ⟨f, hf, hbounded, hgap, hHess, hHessLip, hProb⟩ :=
    hLower Seed seeds N hN (paddedQuery M) (padded_query_measurable M hM)
      (paddedOutput M N) (padded_output_measurable M hM N)
  refine ⟨f, hf, hbounded, hgap, hHess, hHessLip, ?_⟩
  simpa only [actual_padded_output_is_original_early_output] using hProb

end
end FangqingSingleLowerArbitraryFiniteInf
end


section

open MeasureTheory
open scoped ContDiff ENNReal

namespace FangqingBaselineSourceFiniteInf

open FangqingSingleLowerArbitraryFiniteInf FangqingSingleLowerCanonicalEuclidean
  FangqingSingleLowerAllDerivativeOracle FangqingSingleLowerActualOracleProgram
  FangqingSingleLowerFixedFunctionExecution FangqingFixedHorizonSourceMachine
  FangqingSingleLowerEarlyStopPadding OriginalPrefixOracleReplay

noncomputable section
universe v

/-- The actual arbitrary-machine minimax theorem is applied to a genuine Borel
    stop-at-N machine implementing the source queries and terminal output. -/
theorem counterblind_source_program_minimax_lower :
    ∃ c Cdim : ℝ, 0 < c ∧ 0 < Cdim ∧
      ∀ ell rho delta Delta : ℝ, 0 < ell → 0 < rho → 0 < delta → 0 < Delta →
      let T := c * Delta *
        min (ell * delta ^ (-2 : ℝ)) (Real.sqrt rho * delta ^ (-(3 / 2 : ℝ)))
      2 ≤ T → ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ Cdim * T ^ 2 * Real.log T ∧
      letI : MeasurableSpace (Response (EuclideanSpace ℝ (Fin d))) := canonicalResponseMeasurableSpace d
      ∀ (Seed : Type v) [MeasurableSpace Seed] (seeds : Measure Seed) [IsProbabilityMeasure seeds],
      ∀ N : ℕ, (N : ℝ) < T →
      ∀ (q : Query Seed (Response (EuclideanSpace ℝ (Fin d))) (EuclideanSpace ℝ (Fin d))),
        (∀ t, Measurable (fun x : Seed × State (Response (EuclideanSpace ℝ (Fin d))) => q t x.1 x.2)) →
      ∀ (out : Seed → State (Response (EuclideanSpace ℝ (Fin d))) → EuclideanSpace ℝ (Fin d)),
        Measurable (fun x : Seed × State (Response (EuclideanSpace ℝ (Fin d))) => out x.1 x.2) →
      CounterBlindQuery q → CounterBlindOutput out →
      ∃ f : EuclideanSpace ℝ (Fin d) → ℝ,
        ContDiff ℝ ∞ f ∧ BddBelow (Set.range f) ∧ f 0 - sInf (Set.range f) ≤ Delta ∧
        (∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ ell) ∧
        (∀ x y, ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤ rho * ‖x - y‖) ∧
        ∀ baseDimension : ℕ,
          seeds {seed | ‖gradient f (outputOnFunction baseDimension N q out f seed)‖ ≤ delta} ≤ (1 / 3 : ℝ≥0∞) := by
  obtain ⟨c, Cdim, hc, hCdim, hAll⟩ := original_arbitrary_measurable_algorithm_minimax_lower.{v, v}
  refine ⟨c, Cdim, hc, hCdim, ?_⟩
  intro ell rho delta Delta hell hrho hdelta hDelta T hT
  obtain ⟨d, hd, hdim, hLower⟩ := hAll ell rho delta Delta hell hrho hdelta hDelta hT
  refine ⟨d, hd, hdim, ?_⟩
  letI : MeasurableSpace (Response (EuclideanSpace ℝ (Fin d))) := canonicalResponseMeasurableSpace d
  intro Seed instSeed seeds instProb N hN q hq out hout hblind houtblind
  let M := horizonMachine N q out
  have hM : BorelMachine M := horizon_machine_is_borel N q hq out hout
  obtain ⟨f, hf, hbounded, hgap, hHess, hHessLip, hProb⟩ :=
    hLower Seed seeds (StoredState Seed (Response (EuclideanSpace ℝ (Fin d)))) M hM N hN
  refine ⟨f, hf, hbounded, hgap, hHess, hHessLip, ?_⟩
  intro baseDimension
  dsimp only [M] at hProb
  simpa only [actual_machine_output_equals_full_source_output N q out hblind houtblind f baseDimension] using hProb

end
end FangqingBaselineSourceFiniteInf
end
end

section
-- Source component: BaselineFiniteInfInterface.lean

open MeasureTheory
open scoped ContDiff ENNReal

namespace FangqingBaselineFiniteInfInterface

open FangqingBaselineSaddleInterface FangqingLiftOracleJetBridge

noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

structure FiniteInfValid (J : Joint E → ℝ) (L mu rho Delta : ℝ) : Prop extends
    FangqingBaselineSaddleInterface.Valid J L mu rho Delta where
  boundedBelow : BddBelow (Set.range (value J))

theorem actual_large_lift_bounded_below (F : E → ℝ) (hF : ContDiff ℝ 2 F)
    (mu b : ℝ) (c : E) (hmu : 0 < mu) (hB : BddBelow (Set.range F))
    (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ mu) :
    BddBelow (Set.range (value (AllDerivativeLift.jointLift F mu b c))) := by
  have hnorm : ∀ x, ‖fderiv ℝ (gradient F) x‖ ≤ mu := by
    intro x
    rw [actual_hessian_norm_in_gradient_coordinates F hF x]
    exact hH x
  have hd := hF.differentiable (by norm_num)
  have hLip := AllDerivativeLift.gradient_lipschitz_from_hessian_norm F hF mu hnorm
  obtain ⟨m, hm⟩ := hB
  refine ⟨m, ?_⟩
  rintro z ⟨x, rfl⟩
  rw [value_of_large_lift, AllDerivativeLift.phi_eq_at_yStar F mu b c hmu hd hLip]
  have hmax := AllDerivativeLift.yStar_maximizes F mu b c hmu hd hLip x (AllDerivativeLift.center b c x)
  have hlow : m ≤ F (AllDerivativeLift.center b c x) := hm (Set.mem_range_self _)
  exact hlow.trans (by simpa [AllDerivativeLift.lift] using hmax)

theorem large_lift_has_finite_inf_class (F : E → ℝ) (hF : ContDiff ℝ 2 F)
    (L mu kappa rho Delta : ℝ) (hmu : 0 < mu) (hk : 6 ≤ kappa) (hL : mu * kappa = L)
    (hrho : 0 < rho) (hB : BddBelow (Set.range F))
    (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ mu)
    (hHLip : ∀ x y, ‖fderiv ℝ (fderiv ℝ F) x - fderiv ℝ (fderiv ℝ F) y‖ ≤ rho * ‖x - y‖)
    (hgap : F 0 - sInf (Set.range F) ≤ Delta) :
    FiniteInfValid (AllDerivativeLift.jointLift F mu (AllDerivativeLift.scaleB kappa) (AllDerivativeLift.initialShift F mu))
      L mu rho Delta :=
  ⟨large_lift_is_actually_valid F hF L mu kappa rho Delta hmu hk hL hrho hH hHLip hgap,
    actual_large_lift_bounded_below F hF mu _ _ hmu hB hH⟩

theorem decoupled_lift_has_finite_inf_class (F : E → ℝ) (hF : ContDiff ℝ 2 F)
    (L mu rho Delta : ℝ) (hmu : 0 < mu) (hmL : mu ≤ L) (hrho : 0 ≤ rho)
    (hB : BddBelow (Set.range F)) (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ L)
    (hHLip : ∀ x y, ‖fderiv ℝ (fderiv ℝ F) x - fderiv ℝ (fderiv ℝ F) y‖ ≤ rho * ‖x - y‖)
    (hgap : F 0 - sInf (Set.range F) ≤ Delta) :
    FiniteInfValid (FangqingDecoupledLowerLift.objective F mu) L mu rho Delta := by
  refine ⟨decoupled_lift_is_actually_valid F hF L mu rho Delta hmu hmL hrho hH hHLip hgap, ?_⟩
  simpa only [value_of_decoupled_lift, FangqingDecoupledLowerLift.actual_value_equals_F F mu hmu.le] using hB

end
end FangqingBaselineFiniteInfInterface
end

section
-- Source component: BaselineZeroQueryFiniteInf.lean

open MeasureTheory
open scoped ContDiff ENNReal

namespace FangqingBaselineZeroQueryFiniteInf

open FangqingBaselineFiniteInfInterface OriginalPrefixOracleReplay FangqingLiftOracleJetBridge FangqingBaselineSaddleInterface
  FangqingZeroQueryQuadraticLower

noncomputable section
universe v

theorem actual_zero_query_saddle_minimax (L mu rho eps Delta : ℝ)
    (hL : 0 < L) (hmu : 0 < mu) (hmL : mu ≤ L) (hrho : 0 ≤ rho)
    (heps : 0 < eps) (hgap : 5 * eps ^ 2 ≤ Delta * L) :
    let E := EuclideanSpace ℝ (Fin 1)
    letI : MeasurableSpace (Joint E) := borel _
    letI : MeasurableSpace (SaddleResponse E) := borel _
    ∀ (Seed : Type v) [MeasurableSpace Seed] (seeds : Measure Seed) [IsProbabilityMeasure seeds],
    ∀ (q : Query Seed (SaddleResponse E) (Joint E)),
      (∀ t, Measurable (fun x : Seed × State (SaddleResponse E) => q t x.1 x.2)) →
    ∀ (out : Seed → State (SaddleResponse E) → E),
      Measurable (fun x : Seed × State (SaddleResponse E) => out x.1 x.2) →
    ∃ J : Joint E → ℝ, FiniteInfValid J L mu rho Delta ∧
      seeds {seed | ‖gradient (value J) (output J q out 0 seed)‖ ≤ eps} ≤ (1 / 3 : ℝ≥0∞) := by
  intro E
  letI : MeasurableSpace (Joint E) := borel _
  letI : BorelSpace (Joint E) := ⟨rfl⟩
  letI : MeasurableSpace (SaddleResponse E) := borel _
  letI : BorelSpace (SaddleResponse E) := ⟨rfl⟩
  intro Seed instSeed seeds instProb q hq out hout
  let v : E := EuclideanSpace.single (0 : Fin 1) 1
  have hv : ‖v‖ = 1 := by
    change ‖EuclideanSpace.single (0 : Fin 1) (1 : ℝ)‖ = 1
    simpa only [Real.norm_eq_abs, abs_one] using EuclideanSpace.norm_single (0 : Fin 1) (1 : ℝ)
  have hout0 : Measurable (fun seed => out seed (0, 0)) :=
    hout.comp (measurable_id.prodMk measurable_const)
  obtain ⟨F, hF, hBelow, hH, hHLip, hGap, hProb⟩ :=
    fixed_quadratic_defeats_zero_query_output L eps Delta rho hL heps hrho hgap v hv seeds
      (fun seed => out seed (0, 0)) hout0
  refine ⟨FangqingDecoupledLowerLift.objective F mu,
    decoupled_lift_has_finite_inf_class F (hF.of_le (by decide)) L mu rho Delta hmu hmL hrho hBelow hH hHLip hGap, ?_⟩
  rw [value_of_decoupled_lift, FangqingDecoupledLowerLift.actual_value_equals_F F mu hmu.le]
  change seeds {seed | ‖gradient F (out seed (0, 0))‖ ≤ eps} ≤ (1 / 3 : ℝ≥0∞)
  apply (ENNReal.toReal_le_toReal (measure_ne_top seeds _) (by norm_num : (1 / 3 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞))).mp
  have hthird : (1 / 3 : ℝ≥0∞).toReal = (1 / 3 : ℝ) := by norm_num
  rw [hthird]
  exact hProb

end
end FangqingBaselineZeroQueryFiniteInf
end

section
-- Source component: BaselineSaddleFiniteInf.lean

open MeasureTheory
open scoped ContDiff ENNReal

namespace FangqingBaselineSaddleFiniteInf

open FangqingBaselineFiniteInfInterface OriginalPrefixOracleReplay FangqingLiftOracleJetBridge FangqingBaselineSaddleInterface
  FangqingBaselineSourceFiniteInf FangqingBaselineRateScalars FangqingBaselineZeroQueryFiniteInf
  FangqingSingleLowerCanonicalEuclidean FangqingSingleLowerActualOracleProgram
  FangqingFixedHorizonSourceMachine FangqingActualRelayScaling

noncomputable section
set_option maxHeartbeats 8000000
universe v

def HardAtDimension (d : ℕ) (L mu rho eps Delta B : ℝ) : Prop :=
  let E := EuclideanSpace ℝ (Fin d)
  letI : MeasurableSpace (Joint E) := borel _
  letI : MeasurableSpace (SaddleResponse E) := borel _
  ∀ (Seed : Type v) [MeasurableSpace Seed] (seeds : Measure Seed) [IsProbabilityMeasure seeds],
  ∀ N : ℕ, (N : ℝ) < B →
  ∀ (q : Query Seed (SaddleResponse E) (Joint E)),
    (∀ t, Measurable (fun x : Seed × State (SaddleResponse E) => q t x.1 x.2)) →
  ∀ (out : Seed → State (SaddleResponse E) → E),
    Measurable (fun x : Seed × State (SaddleResponse E) => out x.1 x.2) →
  ∃ J : Joint E → ℝ, FiniteInfValid J L mu rho Delta ∧
    seeds {seed | ‖gradient (value J) (output J q out N seed)‖ ≤ eps} ≤ (1 / 3 : ℝ≥0∞)

theorem zero_queries_cover_a_budget_below_one (L mu rho eps Delta B : ℝ)
    (hL : 0 < L) (hmu : 0 < mu) (hmL : mu ≤ L) (hrho : 0 ≤ rho)
    (heps : 0 < eps) (hgap : 5 * eps ^ 2 ≤ Delta * L) (hB : B ≤ 1) :
    HardAtDimension.{v} 1 L mu rho eps Delta B := by
  let E := EuclideanSpace ℝ (Fin 1)
  letI : MeasurableSpace (Joint E) := borel _
  letI : BorelSpace (Joint E) := ⟨rfl⟩
  letI : MeasurableSpace (SaddleResponse E) := borel _
  letI : BorelSpace (SaddleResponse E) := ⟨rfl⟩
  intro Seed instSeed seeds instProb N hN q hq out hout
  have hz : N = 0 := by
    have hh : (N : ℝ) < 1 := hN.trans_le hB
    have hn : N < 1 := by exact_mod_cast hh
    omega
  subst N
  exact actual_zero_query_saddle_minimax L mu rho eps Delta hL hmu hmL hrho heps hgap
    Seed seeds q hq out hout

/-- Complete baseline for the literal full joint O2 run. The rate uses the
    original A1 and r, with a genuine charged bootstrap only in the large-kappa lift. -/
theorem actual_complete_baseline_saddle_minimax :
    ∃ cbase C : ℝ, 0 < cbase ∧ 0 < C ∧
      ∀ L mu eps Delta r : ℝ, 0 < L → 0 < mu → mu ≤ L → 0 < eps → 0 < Delta → 0 < r →
      C ≤ Delta / energy L eps →
      ∃ d : ℕ, 0 < d ∧ HardAtDimension.{v} d L mu
        (FangqingThirdGroupScaling.rho L mu eps r) eps Delta
        (cbase * mass L eps Delta r) := by
  obtain ⟨c, Cdim, hc, hCdim, hSource⟩ := counterblind_source_program_minimax_lower.{v}
  refine ⟨c / 100, max 5 (100 / c), by positivity, by positivity, ?_⟩
  intro L mu eps Delta r hL hmu hmL heps hDelta hr hA
  let kappa := L / mu
  let rho := FangqingThirdGroupScaling.rho L mu eps r
  let B := (c / 100) * mass L eps Delta r
  have hkpos : 0 < kappa := div_pos hL hmu
  have hk1 : 1 ≤ kappa := (le_div_iff₀ hmu).mpr (by simpa using hmL)
  have hrel : mu * kappa = L := by dsimp [kappa]; field_simp
  have hrho : 0 < rho := by dsimp [rho, FangqingThirdGroupScaling.rho]; positivity
  have hA5 : 5 ≤ Delta / energy L eps := (le_max_left 5 (100 / c)).trans hA
  have hGap : 5 * eps ^ 2 ≤ Delta * L := by
    dsimp [energy] at hA5
    have hh := (le_div_iff₀ (by positivity : 0 < eps ^ 2 / L)).mp hA5
    have hm := mul_le_mul_of_nonneg_right hh hL.le
    field_simp [hL.ne'] at hm
    nlinarith only [hm]
  have hMpos : 0 < mass L eps Delta r := by
    dsimp [mass, energy]
    positivity
  by_cases hk : 6 ≤ kappa
  · let b := AllDerivativeLift.scaleB kappa
    let delta := 3 * eps / (2 * b)
    let T := sourceRate c mu rho delta Delta
    have hb : 0 < b := (AllDerivativeLift.scaleB_properties kappa hk).1
    have hd : 0 < delta := by dsimp [delta]; positivity
    have hterms := large_kappa_rate_terms L mu kappa eps r hL hmu heps hr hk hrel
    have hRate : (c / 9) * mass L eps Delta r ≤ T :=
      rate_dominates_baseline_mass c mu rho delta L eps Delta r hc hL heps hDelta hrho.le hd hterms.1 hterms.2
    have hBT : 2 * B ≤ T := by dsimp [B]; nlinarith only [hRate, hc, hMpos]
    by_cases hT : 2 ≤ T
    · obtain ⟨d, hdpos, hdim, hHard⟩ := hSource mu rho delta Delta hmu hrho hd hDelta hT
      refine ⟨d, hdpos, ?_⟩
      let E := EuclideanSpace ℝ (Fin d)
      letI : MeasurableSpace (Joint E) := borel _
      letI : BorelSpace (Joint E) := ⟨rfl⟩
      letI : MeasurableSpace (SaddleResponse E) := borel _
      letI : BorelSpace (SaddleResponse E) := ⟨rfl⟩
      letI : MeasurableSpace (FangqingSingleLowerAllDerivativeOracle.AllDerivativeResponse E) := canonicalResponseMeasurableSpace d
      letI : BorelSpace (FangqingSingleLowerAllDerivativeOracle.AllDerivativeResponse E) := canonical_response_borel d
      intro Seed instSeed seeds instProb N hN q hq out hout
      have hNK : ((N + 1 : ℕ) : ℝ) < T := bootstrap_query_is_absorbed T B N hT hBT hN
      obtain ⟨F, hF, hFbounded, hFGap, hFH, hFHLip, hProb⟩ := hHard Seed seeds (N + 1) hNK
        (FangqingAllDerivativeLiftExecution.sourceQuery mu b q)
        (FangqingAllDerivativeLiftExecution.source_query_measurable mu b q hq)
        (FangqingAllDerivativeLiftExecution.sourceOutput mu b q out N)
        (FangqingAllDerivativeLiftExecution.source_output_measurable mu b q hq out hout N)
        (by intro t seed k h; cases t <;> rfl) (by intro seed k h; rfl)
      let J := AllDerivativeLift.jointLift F mu b (AllDerivativeLift.initialShift F mu)
      refine ⟨J, large_lift_has_finite_inf_class F (hF.of_le (by decide)) L mu kappa rho Delta
        hmu hk hrel hrho hFbounded hFH hFHLip hFGap, ?_⟩
      have hh := FangqingAllDerivativeLiftExecution.actual_saddle_success_probability_le_source_success seeds F
        (hF.of_le (by decide)) mu b eps hmu hb hFH q out 0 N
      have hp := hProb 0
      have heq : (3 / (2 * b)) * eps = delta := by dsimp [delta]; ring
      rw [heq] at hh
      have hbound := hh.trans hp
      simpa only [J, value_of_large_lift, output_of_large_lift] using hbound
    · have hB : B ≤ 1 := by linarith only [hBT, hT]
      exact ⟨1, by norm_num, zero_queries_cover_a_budget_below_one L mu rho eps Delta B hL hmu hmL hrho.le heps hGap hB⟩
  · let T := sourceRate c L rho eps Delta
    have hk6 : kappa < 6 := lt_of_not_ge hk
    have hterms := small_kappa_rate_terms L kappa eps r hL heps hr hkpos hk6
    have hRate : (c / 9) * mass L eps Delta r ≤ T :=
      rate_dominates_baseline_mass c L rho eps L eps Delta r hc hL heps hDelta hrho.le heps hterms.1 hterms.2
    have hBT : 2 * B ≤ T := by dsimp [B]; nlinarith only [hRate, hc, hMpos]
    by_cases hT : 2 ≤ T
    · obtain ⟨d, hdpos, hdim, hHard⟩ := hSource L rho eps Delta hL hrho heps hDelta hT
      refine ⟨d, hdpos, ?_⟩
      let E := EuclideanSpace ℝ (Fin d)
      letI : MeasurableSpace (Joint E) := borel _
      letI : BorelSpace (Joint E) := ⟨rfl⟩
      letI : MeasurableSpace (SaddleResponse E) := borel _
      letI : BorelSpace (SaddleResponse E) := ⟨rfl⟩
      letI : MeasurableSpace (FangqingSingleLowerAllDerivativeOracle.AllDerivativeResponse E) := canonicalResponseMeasurableSpace d
      letI : BorelSpace (FangqingSingleLowerAllDerivativeOracle.AllDerivativeResponse E) := canonical_response_borel d
      intro Seed instSeed seeds instProb N hN q hq out hout
      have hNK : (N : ℝ) < T := by
        have hNB : (N : ℝ) < B := hN
        linarith only [hNB, hBT, (show (0 : ℝ) ≤ (N : ℝ) from Nat.cast_nonneg N)]
      obtain ⟨F, hF, hFbounded, hFGap, hFH, hFHLip, hProb⟩ := hHard Seed seeds N hNK
        (FangqingDecoupledLowerLiftExecution.sourceQuery mu q)
        (FangqingDecoupledLowerLiftExecution.source_query_measurable mu q hq)
        (FangqingDecoupledLowerLiftExecution.sourceOutput mu q out N)
        (FangqingDecoupledLowerLiftExecution.source_output_measurable mu q hq out hout N)
        (by intro t seed k h; rfl) (by intro seed k h; rfl)
      let J := FangqingDecoupledLowerLift.objective F mu
      refine ⟨J, decoupled_lift_has_finite_inf_class F (hF.of_le (by decide)) L mu rho Delta
        hmu hmL hrho.le hFbounded hFH hFHLip hFGap, ?_⟩
      have hh := FangqingDecoupledLowerLiftExecution.actual_success_probability_is_the_same_source_probability seeds F
        (hF.of_le (by decide)) mu eps hmu.le q out 0 N
      have hp := hProb 0
      rw [← hh] at hp
      simpa only [J, value_of_decoupled_lift, output_of_decoupled_lift] using hp
    · have hB : B ≤ 1 := by linarith only [hBT, hT]
      exact ⟨1, by norm_num, zero_queries_cover_a_budget_below_one L mu rho eps Delta B hL hmu hmL hrho.le heps hGap hB⟩

end
end FangqingBaselineSaddleFiniteInf
end

section
-- Source component: CompositionOriginalTheorem.lean

open MeasureTheory
open scoped ENNReal

namespace FangqingCompositionOriginalTheorem

open FangqingCanonicalHierarchyGlobalWorld FangqingCanonicalHierarchyProduct
  FangqingCompositionParameterSelection FangqingCompositionEuclideanSuccessBound
  FangqingCanonicalProductGradientFailure FangqingOriginalWorldExecutionCoordinates
  FangqingActualPaddedRelayReplies FangqingActualRelayScaling FangqingThirdGroupScaling
  FangqingBaselineSaddleFiniteInf FangqingBaselineRateScalars

noncomputable section
set_option maxHeartbeats 6500000
universe v

/-- Actual full-F_T Euclidean execution branch; its dimension is fixed before algorithms.
The other branch below is the independently established genuine baseline saddle execution.
Both branches assert fixed-instance hardness for every Borel randomized full-jet algorithm. -/
def RelayHardAtRate (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Cm Cw : ℝ)
    (H : HierarchyConstants.{0} P phi Cm Cw) (L mu eps r Delta B : ℝ) : Prop :=
  ∃ s : SelectedParameters P phi Cm Cw H L mu eps r Delta,
  ∀ (Seed : Type v) [MeasurableSpace Seed] (seeds : Measure Seed) [IsProbabilityMeasure seeds]
    (query : OriginalQuery Seed (EuclideanBlock s.d) (EuclideanBlock s.d) (EuclideanBlock s.d) s.outer)
    (out : OriginalOutput Seed (EuclideanBlock s.d) (EuclideanBlock s.d) (EuclideanBlock s.d) s.outer)
    (hqMeas : ∀ n, Measurable (fun x : Seed × Point (EuclideanBlock s.d) (EuclideanBlock s.d) (EuclideanBlock s.d) s.outer ×
      (ℕ → Response (EuclideanBlock s.d) (EuclideanBlock s.d) (EuclideanBlock s.d) s.outer) => query n x.1 x.2.1 x.2.2))
    (hout : Measurable (fun x : Seed × Point (EuclideanBlock s.d) (EuclideanBlock s.d) (EuclideanBlock s.d) s.outer ×
      (ℕ → Response (EuclideanBlock s.d) (EuclideanBlock s.d) (EuclideanBlock s.d) s.outer) => out x.1 x.2.1 x.2.2))
    (N : ℕ) (hN : (N:ℝ) < B),
    VerifiedSelectedWorldOutcome P phi Cm Cw H L mu eps r Delta s query out N seeds

/-- A choice between two fully specified legal finite-dimensional oracle families.
This is a disjunction of actual execution theorems, not assumed failure probabilities. -/
def UnrestrictedHardAtRate (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Cm Cw : ℝ)
    (H : HierarchyConstants.{0} P phi Cm Cw) (L mu eps r Delta B : ℝ) : Prop :=
  (∃ d : ℕ, 0 < d ∧ HardAtDimension.{v} d L mu (rho L mu eps r) eps Delta B) ∨
    RelayHardAtRate.{v} P phi Cm Cw H L mu eps r Delta B

theorem actual_baseline_hardness_is_monotone (d : ℕ) (L mu rho eps Delta B B0 : ℝ)
    (h : HardAtDimension.{v} d L mu rho eps Delta B0) (hB : B ≤ B0) :
    HardAtDimension.{v} d L mu rho eps Delta B := by
  intro Seed instSeed seeds instProb N hN q hq out hout
  exact h Seed seeds N (hN.trans_le hB) q hq out hout

/-- Whole original private-handle composition, including the bounded packet-length branch.
The universal H/c/C precede parameters, dimensions, algorithms and realized seeds. -/
theorem original_private_handle_composition
    (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Bp left right Cm Cw : ℝ)
    (hCm : 4 ≤ Cm) (hCw : 4*(Cm+2) ≤ Cw)
    (hp : ContDiff ℝ 3 phi) (hl : ∀ t, t < -Bp → phi t = left)
    (hrp : ∀ t, Bp < t → phi t = right) (hcore : ∀ t, |t| < 1 → phi t = t) :
    ∃ (H : HierarchyConstants.{0} P phi Cm Cw) (c C : ℝ), 0 < c ∧ 0 < C ∧
      ∀ L mu eps Delta r : ℝ, 0 < L → 0 < mu → mu ≤ L → 0 < eps → 0 < Delta → 1 ≤ r →
      C ≤ Delta/energy L eps →
      UnrestrictedHardAtRate.{v} P phi Cm Cw H L mu eps r Delta
        (c*(Delta/energy L eps)*rateFactor r (L/mu)) := by
  obtain ⟨H⟩ := exists_same_actual_hierarchy P phi Bp left right Cm Cw (by linarith only [hCm]) hCw hp hl hrp hcore
  obtain ⟨cbase,Cbase,hcbase,hCbase,hBase⟩ := actual_complete_baseline_saddle_minimax.{v}
  let c := min (compositionRateConstant P phi Cm Cw H) (cbase*H.cq/128)
  let C := max Cbase (2/H.cT)
  have hcT := H.hcT
  have hcq := H.hcq
  have hc : 0 < c := by dsimp [c,compositionRateConstant]; positivity
  have hC : 0 < C := hCbase.trans_le (le_max_left _ _)
  refine ⟨H,c,C,hc,hC,?_⟩
  intro L mu eps Delta r hL hmu hmL heps hDelta hr hA
  have hApos : 0 < Delta/energy L eps := by unfold energy; positivity
  have hm : 0 ≤ rateFactor r (L/mu) := by unfold rateFactor; positivity
  by_cases hLarge : 128 ≤ H.cq*rateFactor r (L/mu)
  · right
    obtain ⟨s,hs⟩ := select_actual_euclidean_composition_family_with_success_bound P phi Cm Cw H hCm hCw hp hcore
      L mu eps r Delta hL hmu heps hr hDelta.le ((le_max_right _ _).trans hA) hLarge
    refine ⟨s,?_⟩
    intro Seed instSeed seeds instProb query out hq ho N hN
    have hB : c*(Delta/energy L eps)*rateFactor r (L/mu) ≤
        compositionRateConstant P phi Cm Cw H*(Delta/energy L eps)*rateFactor r (L/mu) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left _ _) hApos.le) hm
    exact hs Seed seeds query out hq ho N (hN.trans_le hB)
  · left
    have hsmall : H.cq*rateFactor r (L/mu) < 128 := lt_of_not_ge hLarge
    have hcSmall : c ≤ cbase*H.cq/128 := min_le_right _ _
    have hCmRate : c*rateFactor r (L/mu) ≤ cbase := by
      have hm1 := mul_le_mul_of_nonneg_right hcSmall hm
      have hm2 := mul_lt_mul_of_pos_left hsmall hcbase
      nlinarith only [hm1,hm2]
    have hB : c*(Delta/energy L eps)*rateFactor r (L/mu) ≤ cbase*(Delta/energy L eps) := by
      have hm1 := mul_le_mul_of_nonneg_right hCmRate hApos.le
      nlinarith only [hm1]
    have hsqrt : 1 ≤ Real.sqrt r := Real.one_le_sqrt.mpr hr
    obtain ⟨d,hd,hHard⟩ := hBase L mu eps Delta r hL hmu hmL heps hDelta (zero_lt_one.trans_le hr)
      ((le_max_left _ _).trans hA)
    have hHard' : HardAtDimension.{v} d L mu (rho L mu eps r) eps Delta (cbase*(Delta/energy L eps)) := by
      simpa only [mass,min_eq_left hsqrt,mul_one] using hHard
    exact ⟨d,hd,actual_baseline_hardness_is_monotone d L mu (rho L mu eps r) eps Delta _ _ hHard' hB⟩

end
end FangqingCompositionOriginalTheorem
end

section
-- Source component: ThreePhaseFrontierScalars.lean

namespace OriginalThreePhaseScalars

noncomputable def upperFactor (kappa r : ℝ) : ℝ :=
  min (Real.sqrt r * (1 + r ^ (1 / 7 : ℝ))) (min (1 + r ^ (2 / 7 : ℝ)) (Real.sqrt kappa))

noncomputable def frontier (kappa r : ℝ) : ℝ :=
  if r ≤ 1 then Real.sqrt r
  else if r ≤ kappa ^ (7 / 4 : ℝ) then r ^ (2 / 7 : ℝ)
  else Real.sqrt kappa

theorem first_phase_bounds (kappa r : ℝ) (hk : 1 ≤ kappa) (hr : 0 < r) (hr1 : r ≤ 1) :
    Real.sqrt r ≤ upperFactor kappa r ∧ upperFactor kappa r ≤ 2 * Real.sqrt r := by
  have hr0 := hr.le
  have hsr := Real.sqrt_nonneg r
  have hsk := Real.sqrt_nonneg kappa
  have hsr1 : Real.sqrt r ≤ 1 := (Real.sqrt_le_one).mpr hr1
  have hsk1 : 1 ≤ Real.sqrt kappa := (Real.one_le_sqrt).mpr hk
  have hp0 : 0 ≤ r ^ (1 / 7 : ℝ) := Real.rpow_nonneg hr0 _
  have hp1 : r ^ (1 / 7 : ℝ) ≤ 1 := Real.rpow_le_one hr0 hr1 (by norm_num)
  have hq0 : 0 ≤ r ^ (2 / 7 : ℝ) := Real.rpow_nonneg hr0 _
  constructor
  · unfold upperFactor
    exact le_min (by nlinarith only [hsr, hp0])
      (le_min (by linarith only [hsr1, hq0]) (hsr1.trans hsk1))
  · exact (min_le_left _ _).trans (by nlinarith only [hsr, hp1] : Real.sqrt r * (1 + r ^ (1 / 7 : ℝ)) ≤ _)

theorem threshold_rpow_identity (kappa : ℝ) (hk : 0 ≤ kappa) :
    (kappa ^ (7 / 4 : ℝ)) ^ (2 / 7 : ℝ) = Real.sqrt kappa := by
  rw [← Real.rpow_mul hk]
  norm_num only [show (7 / 4 : ℝ) * (2 / 7) = 1 / 2 by norm_num]
  exact (Real.sqrt_eq_rpow kappa).symm

theorem second_phase_bounds (kappa r : ℝ) (hk : 1 ≤ kappa) (hr : 1 ≤ r)
    (hphase : r ≤ kappa ^ (7 / 4 : ℝ)) :
    r ^ (2 / 7 : ℝ) ≤ upperFactor kappa r ∧ upperFactor kappa r ≤ 2 * r ^ (2 / 7 : ℝ) := by
  have hr0 : 0 ≤ r := le_trans (by norm_num) hr
  have hk0 : 0 ≤ kappa := le_trans (by norm_num) hk
  have hq : 1 ≤ r ^ (2 / 7 : ℝ) := Real.one_le_rpow hr (by norm_num)
  have hs : r ^ (2 / 7 : ℝ) ≤ Real.sqrt r := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hr (by norm_num)
  have hcap : r ^ (2 / 7 : ℝ) ≤ Real.sqrt kappa := by
    rw [← threshold_rpow_identity kappa hk0]
    exact Real.rpow_le_rpow hr0 hphase (by norm_num)
  have hp : 0 ≤ r ^ (1 / 7 : ℝ) := Real.rpow_nonneg hr0 _
  have hsr := Real.sqrt_nonneg r
  constructor
  · unfold upperFactor
    exact le_min (hs.trans (by nlinarith only [hp, hsr])) (le_min (by linarith) hcap)
  · unfold upperFactor
    exact (min_le_right _ _).trans ((min_le_left _ _).trans (by linarith only [hq]))

theorem third_phase_identity (kappa r : ℝ) (hk : 1 ≤ kappa)
    (hphase : kappa ^ (7 / 4 : ℝ) ≤ r) : upperFactor kappa r = Real.sqrt kappa := by
  have hk0 : 0 ≤ kappa := le_trans (by norm_num) hk
  have hthreshold : kappa ≤ kappa ^ (7 / 4 : ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hk (by norm_num : (1 : ℝ) ≤ 7 / 4)
  have hr0 : 0 ≤ r := hk0.trans (hthreshold.trans hphase)
  have hcap : Real.sqrt kappa ≤ r ^ (2 / 7 : ℝ) := by
    rw [← threshold_rpow_identity kappa hk0]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hk0 _) hphase (by norm_num)
  have hs : Real.sqrt kappa ≤ Real.sqrt r := Real.sqrt_le_sqrt (hthreshold.trans hphase)
  have hp : 0 ≤ r ^ (1 / 7 : ℝ) := Real.rpow_nonneg hr0 _
  have hsr := Real.sqrt_nonneg r
  unfold upperFactor
  apply le_antisymm ((min_le_right _ _).trans (min_le_right _ _))
  exact le_min (hs.trans (by nlinarith only [hp, hsr])) (le_min (by linarith only [hcap]) le_rfl)

theorem complete_scalar_frontier (kappa r : ℝ) (hk : 1 ≤ kappa) (hr : 0 < r) :
    frontier kappa r ≤ upperFactor kappa r ∧ upperFactor kappa r ≤ 2 * frontier kappa r := by
  by_cases hr1 : r ≤ 1
  · simpa only [frontier, if_pos hr1] using first_phase_bounds kappa r hk hr hr1
  · by_cases hphase : r ≤ kappa ^ (7 / 4 : ℝ)
    · simpa only [frontier, if_neg hr1, if_pos hphase] using second_phase_bounds kappa r hk (le_of_not_ge hr1) hphase
    · rw [frontier, if_neg hr1, if_neg hphase, third_phase_identity kappa r hk (le_of_not_ge hphase)]
      exact ⟨le_rfl, by linarith only [Real.sqrt_nonneg kappa]⟩

end OriginalThreePhaseScalars
end

section
-- Source component: CompleteLowerOriginalTheorem.lean

namespace FangqingCompleteLowerOriginalTheorem

open FangqingCompositionOriginalTheorem FangqingCanonicalHierarchyGlobalWorld
  FangqingCompositionParameterSelection FangqingActualRelayScaling FangqingThirdGroupScaling
  FangqingBaselineSaddleFiniteInf FangqingBaselineRateScalars OriginalThreePhaseScalars HandleAlignment

noncomputable section
set_option maxHeartbeats 6000000
universe v

theorem unrestricted_actual_hardness_is_monotone
    (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Cm Cw : ℝ)
    (H : HierarchyConstants.{0} P phi Cm Cw) (L mu eps r Delta B B0 : ℝ)
    (h : UnrestrictedHardAtRate.{v} P phi Cm Cw H L mu eps r Delta B0) (hB : B ≤ B0) :
    UnrestrictedHardAtRate.{v} P phi Cm Cw H L mu eps r Delta B := by
  rcases h with ⟨d,hd,hBase⟩ | ⟨s,hs⟩
  · exact Or.inl ⟨d,hd,actual_baseline_hardness_is_monotone d L mu (rho L mu eps r) eps Delta B B0 hBase hB⟩
  · exact Or.inr ⟨s,fun Seed _ seeds _ query out hq ho N hN => hs Seed seeds query out hq ho N (hN.trans_le hB)⟩

theorem original_large_regime_multiplier_is_exact_psi (kappa r : ℝ)
    (hk : 1 ≤ kappa) (hr : 1 < r) : OriginalThreePhaseScalars.frontier kappa r = rateFactor r kappa := by
  have hr1 : ¬r≤1 := not_le.mpr hr
  have hk0 : 0 ≤ kappa := by linarith only [hk]
  unfold OriginalThreePhaseScalars.frontier rateFactor
  rw [if_neg hr1]
  by_cases hp : r ≤ kappa^(7/4:ℝ)
  · rw [if_pos hp,min_eq_left]
    rw [← threshold_rpow_identity kappa hk0]
    exact Real.rpow_le_rpow (by linarith only [hr] : 0 ≤ r) hp (by norm_num)
  · rw [if_neg hp,min_eq_right]
    rw [← threshold_rpow_identity kappa hk0]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hk0 _) (le_of_not_ge hp) (by norm_num)

theorem original_complete_lower
    (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Bp left right Cm Cw : ℝ)
    (hCm : 4 ≤ Cm) (hCw : 4*(Cm+2) ≤ Cw)
    (hp : ContDiff ℝ 3 phi) (hl : ∀ t, t < -Bp → phi t = left)
    (hrp : ∀ t, Bp < t → phi t = right) (hcore : ∀ t, |t| < 1 → phi t = t) :
    ∃ (H : HierarchyConstants.{0} P phi Cm Cw) (c C : ℝ), 0 < c ∧ 0 < C ∧
      ∀ L mu eps Delta r : ℝ, 0 < L → 0 < mu → mu ≤ L → 0 < eps → 0 < Delta → 0 < r →
      C ≤ Delta/energy L eps →
      UnrestrictedHardAtRate.{v} P phi Cm Cw H L mu eps r Delta
        (c*(Delta/energy L eps)*OriginalThreePhaseScalars.frontier (L/mu) r) := by
  obtain ⟨H,cComp,CComp,hcComp,hCComp,hComp⟩ :=
    original_private_handle_composition P phi Bp left right Cm Cw hCm hCw hp hl hrp hcore
  obtain ⟨cBase,CBase,hcBase,hCBase,hBase⟩ := actual_complete_baseline_saddle_minimax.{v}
  let c := min cComp cBase
  let C := max CComp CBase
  refine ⟨H,c,C,lt_min hcComp hcBase,hCComp.trans_le (le_max_left _ _),?_⟩
  intro L mu eps Delta r hL hmu hmL heps hDelta hr hA
  have hApos : 0 < Delta/energy L eps := by unfold energy; positivity
  have hk : 1 ≤ L/mu := (one_le_div hmu).mpr hmL
  by_cases hr1 : r≤1
  · have hsqrt : Real.sqrt r ≤ 1 := Real.sqrt_le_one.mpr hr1
    obtain ⟨d,hd,hHard⟩ := hBase L mu eps Delta r hL hmu hmL heps hDelta hr ((le_max_right _ _).trans hA)
    have hB : c*(Delta/energy L eps)*OriginalThreePhaseScalars.frontier (L/mu) r ≤ cBase*mass L eps Delta r := by
      simp only [OriginalThreePhaseScalars.frontier,if_pos hr1,mass,min_eq_right hsqrt]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_right cComp cBase) hApos.le) (Real.sqrt_nonneg r)
    exact Or.inl ⟨d,hd,actual_baseline_hardness_is_monotone d L mu (rho L mu eps r) eps Delta _ _ hHard hB⟩
  · have hgt : 1<r := lt_of_not_ge hr1
    have hHard := hComp L mu eps Delta r hL hmu hmL heps hDelta hgt.le ((le_max_left _ _).trans hA)
    have hPsi := original_large_regime_multiplier_is_exact_psi (L/mu) r hk hgt
    have hm : 0 ≤ rateFactor r (L/mu) := by unfold rateFactor; positivity
    apply unrestricted_actual_hardness_is_monotone P phi Cm Cw H L mu eps r Delta _ _ hHard
    rw [hPsi]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left _ _) hApos.le) hm

theorem external_curvature_reparameterization (L mu eps rh : ℝ)
    (hL : 0 < L) (hmu : 0 < mu) (heps : 0 < eps) :
    rho L mu eps (regime L rh eps (L/mu)) = rh := by
  have hk : 0 < L/mu := div_pos hL hmu
  have hs : 0 < Real.sqrt (L/mu) := Real.sqrt_pos.mpr hk
  unfold rho regime
  rw [HandleAlignment.rpow_three_halves (L/mu) hk]
  field_simp

/-- Exact original external rho, r and A1, with the full actual oracle hard family. -/
theorem original_complete_lower_external_parameters
    (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Bp left right Cm Cw : ℝ)
    (hCm : 4 ≤ Cm) (hCw : 4*(Cm+2) ≤ Cw)
    (hp : ContDiff ℝ 3 phi) (hl : ∀ t, t < -Bp → phi t = left)
    (hrp : ∀ t, Bp < t → phi t = right) (hcore : ∀ t, |t| < 1 → phi t = t) :
    ∃ (H : HierarchyConstants.{0} P phi Cm Cw) (c C : ℝ), 0 < c ∧ 0 < C ∧
      ∀ L mu rh eps Delta : ℝ, 0 < L → 0 < mu → mu ≤ L → 0 < rh → 0 < eps → 0 < Delta →
      C ≤ Delta*L/eps^2 →
      let r := regime L rh eps (L/mu)
      rho L mu eps r = rh ∧
      UnrestrictedHardAtRate.{v} P phi Cm Cw H L mu eps r Delta
        (c*(Delta*L/eps^2)*OriginalThreePhaseScalars.frontier (L/mu) r) := by
  obtain ⟨H,c,C,hc,hC,hAll⟩ := original_complete_lower P phi Bp left right Cm Cw hCm hCw hp hl hrp hcore
  refine ⟨H,c,C,hc,hC,?_⟩
  intro L mu rh eps Delta hL hmu hmL hrh heps hDelta hA r
  have hr : 0 < r := by dsimp [r,regime]; positivity
  have hEnergy : Delta/energy L eps = Delta*L/eps^2 := by unfold energy; field_simp [heps.ne',hL.ne']
  refine ⟨external_curvature_reparameterization L mu eps rh hL hmu heps,?_⟩
  rw [← hEnergy]
  exact hAll L mu eps Delta r hL hmu hmL heps hDelta hr (by simpa only [hEnergy] using hA)

end
end FangqingCompleteLowerOriginalTheorem
end

section
-- Source component: CanonicalSeedProfile.lean

open scoped ContDiff

namespace FangqingCanonicalSeedProfile

open FangqingPublicShellProfiles FangqingSaturatedProfileBounds

noncomputable section
set_option maxHeartbeats 2000000

def saturatedSign (t : ℝ) : ℝ := 2*(Real.smoothTransition (t+1)-Real.smoothTransition (1-t))

/-- A fixed odd smooth saturation: identity near zero, constants -2/+2 on the tails. -/
def seedProfile (t : ℝ) : ℝ := t*theta (t^2)+saturatedSign t*(1-theta (t^2))

theorem seed_profile_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) seedProfile := by
  unfold seedProfile saturatedSign
  have htheta := theta_smooth.comp (contDiff_id.pow 2 : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (fun t : ℝ => t^2))
  fun_prop

theorem seed_profile_C3 : ContDiff ℝ 3 seedProfile := seed_profile_smooth.of_le (by decide)

theorem seed_profile_odd (t : ℝ) : seedProfile (-t) = -seedProfile t := by
  have h1 : -t+1=1-t := by ring
  have h2 : 1-(-t)=t+1 := by ring
  simp only [seedProfile,saturatedSign,neg_sq,h1,h2]
  ring

theorem seed_profile_identity_core (t : ℝ) (ht : |t| ≤ 1) : seedProfile t = t := by
  have hs : t^2 ≤ 1 := by
    simpa only [one_pow,sq_abs] using (sq_le_sq₀ (abs_nonneg t) (by norm_num : (0:ℝ)≤1)).mpr ht
  have hth : theta (t^2)=1 := theta_one (t^2) (by nlinarith only [hs])
  simp only [seedProfile,hth,mul_one,sub_self,mul_zero,add_zero]

theorem seed_profile_left_tail (t : ℝ) (ht : t < -(2:ℝ)) : seedProfile t = -2 := by
  have hth : theta (t^2)=0 := theta_zero _ (by nlinarith only [ht,sq_nonneg (t+2)])
  have hs1 : Real.smoothTransition (t+1)=0 := Real.smoothTransition.zero_of_nonpos (by linarith only [ht])
  have hs2 : Real.smoothTransition (1-t)=1 := Real.smoothTransition.one_of_one_le (by linarith only [ht])
  simp only [seedProfile,saturatedSign,hth,hs1,hs2]
  ring

theorem seed_profile_right_tail (t : ℝ) (ht : (2:ℝ) < t) : seedProfile t = 2 := by
  have hth : theta (t^2)=0 := theta_zero _ (by nlinarith only [ht,sq_nonneg (t-2)])
  have hs1 : Real.smoothTransition (t+1)=1 := Real.smoothTransition.one_of_one_le (by linarith only [ht])
  have hs2 : Real.smoothTransition (1-t)=0 := Real.smoothTransition.zero_of_nonpos (by linarith only [ht])
  simp only [seedProfile,saturatedSign,hth,hs1,hs2]
  ring

theorem seed_profile_derivatives_bounded :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ j, j ≤ 3 → ∀ t : ℝ, ‖iteratedFDeriv ℝ j seedProfile t‖ ≤ K :=
  scalar_saturation_derivatives_bounded seedProfile 3 2 (-2) 2 seed_profile_C3
    seed_profile_left_tail seed_profile_right_tail

theorem seed_profile_original_hypotheses :
    ContDiff ℝ 3 seedProfile ∧
    (∀ t, t < -(2:ℝ) → seedProfile t = -2) ∧
    (∀ t, (2:ℝ) < t → seedProfile t = 2) ∧
    (∀ t, |t|<1 → seedProfile t=t) :=
  ⟨seed_profile_C3,seed_profile_left_tail,seed_profile_right_tail,
    fun t ht => seed_profile_identity_core t ht.le⟩

end
end FangqingCanonicalSeedProfile
end

section
-- Source component: CanonicalSeedProfileFullProperties.lean

open scoped Topology

namespace FangqingCanonicalSeedProfile

noncomputable section

theorem seed_profile_derivative_zero_outside (t : ℝ) (ht : 3 ≤ |t|) : deriv seedProfile t = 0 := by
  rcases le_abs.mp ht with hp | hn
  · have he : seedProfile =ᶠ[𝓝 t] (fun _ => (2:ℝ)) := by
      filter_upwards [Ioi_mem_nhds (show (2:ℝ)<t by linarith only [hp])] with x hx
      exact seed_profile_right_tail x hx
    rw [he.deriv_eq,deriv_const]
  · have he : seedProfile =ᶠ[𝓝 t] (fun _ => (-2:ℝ)) := by
      filter_upwards [Iio_mem_nhds (show t < -(2:ℝ) by linarith only [hn])] with x hx
      exact seed_profile_left_tail x hx
    rw [he.deriv_eq,deriv_const]

/-- Concrete nonempty original bounded odd saturated-linear profile interface. -/
theorem canonical_original_seed_profile_exists :
    ∃ phi : ℝ → ℝ, ContDiff ℝ 3 phi ∧
      (∀ t, phi (-t) = -phi t) ∧
      (∀ t, |t|≤1 → phi t=t) ∧
      (∀ t, 3≤|t| → deriv phi t=0) ∧
      ∃ K : ℝ, 0≤K ∧ ∀ j, j≤3 → ∀ t : ℝ, ‖iteratedFDeriv ℝ j phi t‖≤K :=
  ⟨seedProfile,seed_profile_C3,seed_profile_odd,seed_profile_identity_core,
    seed_profile_derivative_zero_outside,seed_profile_derivatives_bounded⟩

end
end FangqingCanonicalSeedProfile
end

section
-- Source component: ClosedOriginalLowerTheorems.lean

namespace FangqingClosedOriginalLowerTheorems

open FangqingCanonicalSeedProfile FangqingCanonicalHierarchyGlobalWorld
  FangqingCompositionOriginalTheorem FangqingCompleteLowerOriginalTheorem
  FangqingCompositionParameterSelection FangqingActualRelayScaling FangqingThirdGroupScaling

noncomputable section
universe v

/-- The original composition statement with all scalar profiles explicitly fixed and all
auxiliary-domain nonemptiness obligations discharged, before physical parameters. -/
theorem original_private_handle_composition_closed :
    ∃ (H : HierarchyConstants.{0} FlatCubic.canonicalProfile seedProfile 4 24) (c C : ℝ), 0 < c ∧ 0 < C ∧
      ∀ L mu eps Delta r : ℝ, 0 < L → 0 < mu → mu ≤ L → 0 < eps → 0 < Delta → 1 ≤ r →
      C ≤ Delta/energy L eps →
      UnrestrictedHardAtRate.{v} FlatCubic.canonicalProfile seedProfile 4 24 H L mu eps r Delta
        (c*(Delta/energy L eps)*rateFactor r (L/mu)) := by
  exact original_private_handle_composition FlatCubic.canonicalProfile seedProfile 2 (-2) 2 4 24
    (by norm_num) (by norm_num) seed_profile_C3 seed_profile_left_tail seed_profile_right_tail
    (fun t ht => seed_profile_identity_core t ht.le)

/-- The complete original external-parameter lower frontier, with no extra profile assumptions.
All hard instances come from actual full-O2 executions with finite infimum and exact R_y=0. -/
theorem original_complete_lower_closed :
    ∃ (H : HierarchyConstants.{0} FlatCubic.canonicalProfile seedProfile 4 24) (c C : ℝ), 0 < c ∧ 0 < C ∧
      ∀ L mu rh eps Delta : ℝ, 0 < L → 0 < mu → mu ≤ L → 0 < rh → 0 < eps → 0 < Delta →
      C ≤ Delta*L/eps^2 →
      let r := HandleAlignment.regime L rh eps (L/mu)
      rho L mu eps r = rh ∧
      UnrestrictedHardAtRate.{v} FlatCubic.canonicalProfile seedProfile 4 24 H L mu eps r Delta
        (c*(Delta*L/eps^2)*OriginalThreePhaseScalars.frontier (L/mu) r) := by
  exact original_complete_lower_external_parameters FlatCubic.canonicalProfile seedProfile 2 (-2) 2 4 24
    (by norm_num) (by norm_num) seed_profile_C3 seed_profile_left_tail seed_profile_right_tail
    (fun t ht => seed_profile_identity_core t ht.le)

end
end FangqingClosedOriginalLowerTheorems
end

section
-- Source component: MoreauTransfer.lean

namespace MoreauTransfer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def objective (Φ : E → ℝ) (L : ℝ) (x u : E) : ℝ :=
  Φ u + L * ‖u - x‖ ^ 2

noncomputable def envelope (Φ : E → ℝ) (L : ℝ) (x : E) : ℝ :=
  sInf (Set.range (objective Φ L x))

noncomputable def prox (Φ : E → ℝ) (L : ℝ) (x : E) : E :=
  Classical.epsilon (fun u : E => ∀ v : E, objective Φ L x u ≤ objective Φ L x v)


theorem weakConvex_packet_strongConvex
    (Φ : E → ℝ) (L : ℝ)
    (hweak : ConvexOn ℝ (Set.univ : Set E) (fun u => Φ u + L / 2 * ‖u‖ ^ 2)) :
    StrongConvexOn (Set.univ : Set E) (L + (-2 * L)) Φ := by
  rw [strongConvexOn_iff_convex]
  have heq : (fun u : E => Φ u - (L + (-2 * L)) / 2 * ‖u‖ ^ 2) =
      (fun u : E => Φ u + L / 2 * ‖u‖ ^ 2) := by
    funext u
    ring
  rw [heq]
  exact hweak


theorem packet_is_negative_objective (Φ : E → ℝ) (L : ℝ) (x u : E) :
    PacketCore.saddleValue Φ (-2 * L) (-2 * L) (2 * L) 0 x u =
      - objective Φ L x u := by
  dsimp [PacketCore.saddleValue, objective]
  rw [norm_sub_sq_real, real_inner_comm u x]
  ring


theorem exists_unique_minimizer
    (Φ : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ Φ)
    (hweak : ConvexOn ℝ (Set.univ : Set E) (fun u => Φ u + L / 2 * ‖u‖ ^ 2))
    (x : E) :
    ∃! u : E, ∀ v : E, objective Φ L x u ≤ objective Φ L x v := by
  have hsc := weakConvex_packet_strongConvex Φ L hweak
  obtain ⟨u, hu⟩ := PacketCore.exists_inner_maximizer_finiteDimensional
    Φ L (-2 * L) (-2 * L) (2 * L) 0 hL hsc hdiff x
  have hmin : ∀ v : E, objective Φ L x u ≤ objective Φ L x v := by
    intro v
    have hh := hu v
    rw [packet_is_negative_objective, packet_is_negative_objective] at hh
    linarith
  refine ⟨u, hmin, ?_⟩
  intro v hv
  have hvmax : ∀ z : E,
      PacketCore.saddleValue Φ (-2 * L) (-2 * L) (2 * L) 0 x z ≤
      PacketCore.saddleValue Φ (-2 * L) (-2 * L) (2 * L) 0 x v := by
    intro z
    rw [packet_is_negative_objective, packet_is_negative_objective]
    exact neg_le_neg (hv z)
  exact PacketCore.unique_inner_maximizer Φ L (-2 * L) (-2 * L) (2 * L) 0
    hL hsc hdiff x v u hvmax hu


theorem prox_minimizes
    (Φ : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ Φ)
    (hweak : ConvexOn ℝ (Set.univ : Set E) (fun u => Φ u + L / 2 * ‖u‖ ^ 2))
    (x v : E) :
    objective Φ L x (prox Φ L x) ≤ objective Φ L x v := by
  exact Classical.epsilon_spec (exists_unique_minimizer Φ L hL hdiff hweak x).exists v


theorem envelope_eq_of_minimizer
    (Φ : E → ℝ) (L : ℝ) (x u : E)
    (hmin : ∀ v : E, objective Φ L x u ≤ objective Φ L x v) :
    envelope Φ L x = objective Φ L x u := by
  have hleast : IsLeast (Set.range (objective Φ L x)) (objective Φ L x u) := by
    constructor
    · exact ⟨u, rfl⟩
    · rintro z ⟨v, rfl⟩
      exact hmin v
  exact hleast.csInf_eq


theorem envelope_eq_prox_objective
    (Φ : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ Φ)
    (hweak : ConvexOn ℝ (Set.univ : Set E) (fun u => Φ u + L / 2 * ‖u‖ ^ 2))
    (x : E) :
    envelope Φ L x = objective Φ L x (prox Φ L x) := by
  exact envelope_eq_of_minimizer Φ L x (prox Φ L x) (prox_minimizes Φ L hL hdiff hweak x)


theorem prox_is_unique
    (Φ : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ Φ)
    (hweak : ConvexOn ℝ (Set.univ : Set E) (fun u => Φ u + L / 2 * ‖u‖ ^ 2))
    (x u : E) (hmin : ∀ v : E, objective Φ L x u ≤ objective Φ L x v) :
    u = prox Φ L x := by
  obtain ⟨w, hw, huniq⟩ := exists_unique_minimizer Φ L hL hdiff hweak x
  exact (huniq u hmin).trans (huniq (prox Φ L x) (prox_minimizes Φ L hL hdiff hweak x)).symm


theorem prox_packet_maximizes
    (Φ : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ Φ)
    (hweak : ConvexOn ℝ (Set.univ : Set E) (fun u => Φ u + L / 2 * ‖u‖ ^ 2)) :
    ∀ x z : E,
      PacketCore.saddleValue Φ (-2 * L) (-2 * L) (2 * L) 0 x z ≤
      PacketCore.saddleValue Φ (-2 * L) (-2 * L) (2 * L) 0 x (prox Φ L x) := by
  intro x z
  rw [packet_is_negative_objective, packet_is_negative_objective]
  exact neg_le_neg (prox_minimizes Φ L hL hdiff hweak x z)


theorem prox_first_order
    (Φ : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ Φ)
    (hweak : ConvexOn ℝ (Set.univ : Set E) (fun u => Φ u + L / 2 * ‖u‖ ^ 2))
    (x : E) :
    gradient Φ (prox Φ L x) = (2 * L) • (x - prox Φ L x) := by
  have hh := PacketCore.inner_maximizer_first_order Φ (-2 * L) (-2 * L) (2 * L) 0
    x (prox Φ L x) hdiff (prox_packet_maximizes Φ L hL hdiff hweak x)
  rw [smul_sub]
  convert hh using 1 <;> module


theorem envelope_quadratic_remainder
    (Φ : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ Φ)
    (hweak : ConvexOn ℝ (Set.univ : Set E) (fun u => Φ u + L / 2 * ‖u‖ ^ 2))
    (x z : E) :
    ‖envelope Φ L z - envelope Φ L x -
      inner ℝ ((2 * L) • (x - prox Φ L x)) (z - x)‖ ≤ L * ‖z - x‖ ^ 2 := by
  have hsc := weakConvex_packet_strongConvex Φ L hweak
  have hmax := prox_packet_maximizes Φ L hL hdiff hweak
  obtain ⟨hlo, hup⟩ := PacketCore.value_maximization_gap Φ L (-2 * L) (-2 * L)
    (2 * L) 0 hL hsc hdiff (prox Φ L) hmax x z
  have hid := PacketCore.saddle_outer_remainder Φ (-2 * L) (-2 * L) (2 * L) 0
    x z (prox Φ L x)
  have hcoeff : (2 * L) ^ 2 / (2 * L) = 2 * L := by
    field_simp
    <;> ring
  have hval (w : E) :
      PacketCore.valueFromMaximizers Φ (-2 * L) (-2 * L) (2 * L) 0 (prox Φ L) w =
      - envelope Φ L w := by
    dsimp [PacketCore.valueFromMaximizers]
    rw [packet_is_negative_objective, envelope_eq_prox_objective Φ L hL hdiff hweak w]
  rw [hval, packet_is_negative_objective] at hlo hup
  rw [hcoeff] at hup
  rw [packet_is_negative_objective, packet_is_negative_objective,
    ← envelope_eq_prox_objective Φ L hL hdiff hweak x] at hid
  have hinner : inner ℝ ((-2 * L) • x + (2 * L) • prox Φ L x) (z - x) =
      - inner ℝ ((2 * L) • (x - prox Φ L x)) (z - x) := by
    rw [inner_add_left, inner_smul_left, inner_smul_left, inner_smul_left, inner_sub_left]
    simp only [conj_trivial]
    ring
  rw [hinner] at hid
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> nlinarith only [hlo, hup, hid]


theorem envelope_hasGradientAt
    (Φ : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ Φ)
    (hweak : ConvexOn ℝ (Set.univ : Set E) (fun u => Φ u + L / 2 * ‖u‖ ^ 2))
    (x : E) :
    HasGradientAt (envelope Φ L) ((2 * L) • (x - prox Φ L x)) x := by
  exact PacketCore.hasGradientAt_of_quadratic_remainder _ _ _ L
    (envelope_quadratic_remainder Φ L hL hdiff hweak x)


theorem exact_stationarity_transfer
    (Φ : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ Φ)
    (hweak : ConvexOn ℝ (Set.univ : Set E) (fun u => Φ u + L / 2 * ‖u‖ ^ 2))
    (x : E) :
    gradient (envelope Φ L) x = (2 * L) • (x - prox Φ L x) ∧
      gradient (envelope Φ L) x = gradient Φ (prox Φ L x) := by
  have hE := (envelope_hasGradientAt Φ L hL hdiff hweak x).gradient
  exact ⟨hE, hE.trans (prox_first_order Φ L hL hdiff hweak x).symm⟩


theorem envelope_le_original
    (Φ : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ Φ)
    (hweak : ConvexOn ℝ (Set.univ : Set E) (fun u => Φ u + L / 2 * ‖u‖ ^ 2))
    (x : E) : envelope Φ L x ≤ Φ x := by
  rw [envelope_eq_prox_objective Φ L hL hdiff hweak x]
  have hh := prox_minimizes Φ L hL hdiff hweak x x
  simpa only [objective, sub_self, norm_zero, zero_pow (by omega : 2 ≠ 0), mul_zero, add_zero] using hh


theorem infimum_equality
    (Φ : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ Φ)
    (hweak : ConvexOn ℝ (Set.univ : Set E) (fun u => Φ u + L / 2 * ‖u‖ ^ 2))
    (hbelow : BddBelow (Set.range Φ)) :
    sInf (Set.range (envelope Φ L)) = sInf (Set.range Φ) := by
  have hlower (x : E) : sInf (Set.range Φ) ≤ envelope Φ L x := by
    rw [envelope_eq_prox_objective Φ L hL hdiff hweak x]
    have hh := csInf_le hbelow (Set.mem_range_self (prox Φ L x))
    dsimp [objective]
    have hnonneg : 0 ≤ L * ‖prox Φ L x - x‖ ^ 2 := by positivity
    linarith only [hh, hnonneg]
  have hEbelow : BddBelow (Set.range (envelope Φ L)) := by
    refine ⟨sInf (Set.range Φ), ?_⟩
    rintro z ⟨x, rfl⟩
    exact hlower x
  apply le_antisymm
  · apply le_csInf (Set.range_nonempty Φ)
    rintro z ⟨x, rfl⟩
    exact (csInf_le hEbelow (Set.mem_range_self x)).trans (envelope_le_original Φ L hL hdiff hweak x)
  · apply le_csInf (Set.range_nonempty (envelope Φ L))
    rintro z ⟨x, rfl⟩
    exact hlower x


theorem initial_gap_transfer
    (Φ : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ Φ)
    (hweak : ConvexOn ℝ (Set.univ : Set E) (fun u => Φ u + L / 2 * ‖u‖ ^ 2))
    (hbelow : BddBelow (Set.range Φ))
    (x0 : E) (Δ : ℝ) (hgap : Φ x0 - sInf (Set.range Φ) ≤ Δ) :
    envelope Φ L x0 - sInf (Set.range (envelope Φ L)) ≤ Δ := by
  rw [infimum_equality Φ L hL hdiff hweak hbelow]
  have hh := envelope_le_original Φ L hL hdiff hweak x0
  linarith only [hh, hgap]


theorem prox_displacement_sq_gap
    (Φ : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ Φ)
    (hweak : ConvexOn ℝ (Set.univ : Set E) (fun u => Φ u + L / 2 * ‖u‖ ^ 2))
    (hbelow : BddBelow (Set.range Φ)) (x : E) :
    L * ‖prox Φ L x - x‖ ^ 2 ≤ Φ x - sInf (Set.range Φ) := by
  have hE := envelope_le_original Φ L hL hdiff hweak x
  rw [envelope_eq_prox_objective Φ L hL hdiff hweak x] at hE
  have hPhi := csInf_le hbelow (Set.mem_range_self (prox Φ L x))
  dsimp [objective] at hE
  linarith only [hE, hPhi]


theorem prox_displacement_le_sqrt_initial_gap
    (Φ : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ Φ)
    (hweak : ConvexOn ℝ (Set.univ : Set E) (fun u => Φ u + L / 2 * ‖u‖ ^ 2))
    (hbelow : BddBelow (Set.range Φ))
    (x : E) (Δ : ℝ) (hgap : Φ x - sInf (Set.range Φ) ≤ Δ) :
    ‖prox Φ L x - x‖ ≤ Real.sqrt (Δ / L) := by
  apply Real.le_sqrt_of_sq_le
  apply (le_div_iff₀ hL).2
  have hh := prox_displacement_sq_gap Φ L hL hdiff hweak hbelow x
  nlinarith only [hh, hgap]

end MoreauTransfer
end

section
-- Source component: SaddleTransfer.lean

namespace OriginalSaddleTransfer

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable def phi (f : E → F → ℝ) (x : E) : ℝ := sSup (Set.range (f x))

noncomputable def yStar (f : E → F → ℝ) (x : E) : F :=
  Classical.epsilon (fun y => ∀ z, f x z ≤ f x y)

noncomputable def saddleObjective (f : E → F → ℝ) (L : ℝ) (x u : E) (y : F) : ℝ :=
  f u y + L * ‖u - x‖ ^ 2

noncomputable def saddleEnvelope (f : E → F → ℝ) (L : ℝ) (x : E) : ℝ :=
  sInf (Set.range (fun u : E => sSup (Set.range (saddleObjective f L x u))))

noncomputable def uStar (f : E → F → ℝ) (L : ℝ) (x : E) : E :=
  MoreauTransfer.prox (phi f) L x

noncomputable def vStar (f : E → F → ℝ) (L : ℝ) (x : E) : F :=
  yStar f (uStar f L x)

theorem yStar_maximizes
    (f : E → F → ℝ) (μ : ℝ) (hμ : 0 < μ)
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ (fun y => -f x y))
    (hdiffY : ∀ x : E, Differentiable ℝ (f x))
    (x : E) (y : F) : f x y ≤ f x (yStar f x) := by
  exact Classical.epsilon_spec
    (OriginalSaddleRegularity.exists_inner_maximum f μ hμ hsc hdiffY x) y

theorem phi_eq_value_at_yStar
    (f : E → F → ℝ) (μ : ℝ) (hμ : 0 < μ)
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ (fun y => -f x y))
    (hdiffY : ∀ x : E, Differentiable ℝ (f x)) (x : E) :
    phi f x = f x (yStar f x) := by
  apply IsGreatest.csSup_eq
  constructor
  · exact ⟨yStar f x, rfl⟩
  · rintro z ⟨y, rfl⟩
    exact yStar_maximizes f μ hμ hsc hdiffY x y

theorem saddle_inner_value
    (f : E → F → ℝ) (L μ : ℝ) (hμ : 0 < μ)
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ (fun y => -f x y))
    (hdiffY : ∀ x : E, Differentiable ℝ (f x)) (x u : E) :
    sSup (Set.range (saddleObjective f L x u)) = MoreauTransfer.objective (phi f) L x u := by
  rw [MoreauTransfer.objective, phi_eq_value_at_yStar f μ hμ hsc hdiffY u]
  apply IsGreatest.csSup_eq
  constructor
  · exact ⟨yStar f u, rfl⟩
  · rintro z ⟨y, rfl⟩
    exact add_le_add (yStar_maximizes f μ hμ hsc hdiffY u y) (le_refl _)

theorem saddleEnvelope_eq_moreau
    (f : E → F → ℝ) (L μ : ℝ) (hμ : 0 < μ)
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ (fun y => -f x y))
    (hdiffY : ∀ x : E, Differentiable ℝ (f x)) :
    saddleEnvelope f L = MoreauTransfer.envelope (phi f) L := by
  funext x
  unfold saddleEnvelope MoreauTransfer.envelope
  congr 2
  funext u
  exact saddle_inner_value f L μ hμ hsc hdiffY x u

theorem phi_regular_from_slices
    (f : E → F → ℝ) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hdiffX : ∀ y : F, Differentiable ℝ (fun x => f x y))
    (hdiffY : ∀ x : E, Differentiable ℝ (f x))
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ (fun y => -f x y))
    (hxx : ∀ y : F, ∀ x z : E,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t y) z‖ ≤ L * ‖x - z‖)
    (hxy : ∀ x : E, ∀ y z : F,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t z) x‖ ≤ L * ‖y - z‖) :
    Differentiable ℝ (phi f) ∧
      ConvexOn ℝ (Set.univ : Set E) (fun u => phi f u + L / 2 * ‖u‖ ^ 2) := by
  have heq : phi f = OriginalSaddleRegularity.value f (yStar f) := by
    funext x
    exact phi_eq_value_at_yStar f μ hμ hsc hdiffY x
  have hr := OriginalSaddleRegularity.value_differentiable_and_weakly_convex f L μ
    hL hμ hdiffX hdiffY hsc hxx hxy (yStar f) (yStar_maximizes f μ hμ hsc hdiffY)
  rw [← heq] at hr
  refine ⟨hr.1, ?_⟩
  have hc := strongConvexOn_iff_convex.mp hr.2
  convert hc using 1 <;> (first | rfl | (congr 1; funext u; ring))

theorem phi_hasGradientAt_yStar
    (f : E → F → ℝ) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hdiffX : ∀ y : F, Differentiable ℝ (fun x => f x y))
    (hdiffY : ∀ x : E, Differentiable ℝ (f x))
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ (fun y => -f x y))
    (hxx : ∀ y : F, ∀ x z : E,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t y) z‖ ≤ L * ‖x - z‖)
    (hxy : ∀ x : E, ∀ y z : F,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t z) x‖ ≤ L * ‖y - z‖)
    (x : E) : HasGradientAt (phi f) (gradient (fun t => f t (yStar f x)) x) x := by
  have heq : phi f = OriginalSaddleRegularity.value f (yStar f) := by
    funext z
    exact phi_eq_value_at_yStar f μ hμ hsc hdiffY z
  rw [heq]
  exact OriginalSaddleRegularity.value_hasGradientAt f L μ hL hμ
    hdiffX hdiffY hsc hxx hxy (yStar f) (yStar_maximizes f μ hμ hsc hdiffY) x

theorem exact_transfer_from_slices
    (f : E → F → ℝ) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hdiffX : ∀ y : F, Differentiable ℝ (fun x => f x y))
    (hdiffY : ∀ x : E, Differentiable ℝ (f x))
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ (fun y => -f x y))
    (hxx : ∀ y : F, ∀ x z : E,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t y) z‖ ≤ L * ‖x - z‖)
    (hxy : ∀ x : E, ∀ y z : F,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t z) x‖ ≤ L * ‖y - z‖)
    (hbelow : BddBelow (Set.range (phi f)))
    (x0 : E) (Δ : ℝ) (hgap : phi f x0 - sInf (Set.range (phi f)) ≤ Δ) :
    (∀ x : E,
      gradient (saddleEnvelope f L) x = (2 * L) • (x - uStar f L x) ∧
      gradient (saddleEnvelope f L) x = gradient (phi f) (uStar f L x)) ∧
    saddleEnvelope f L x0 - sInf (Set.range (saddleEnvelope f L)) ≤ Δ ∧
    sInf (Set.range (saddleEnvelope f L)) = sInf (Set.range (phi f)) ∧
    (∀ x : E, ∃! u : E, ∀ v : E,
      sSup (Set.range (saddleObjective f L x u)) ≤
      sSup (Set.range (saddleObjective f L x v))) ∧
    (∀ x : E, ∀ u : E,
      sSup (Set.range (saddleObjective f L x (uStar f L x))) ≤
      sSup (Set.range (saddleObjective f L x u))) ∧
    (∀ x : E, ∀ y : F,
      saddleObjective f L x (uStar f L x) y ≤
      saddleObjective f L x (uStar f L x) (vStar f L x)) := by
  obtain ⟨hdiff, hweak⟩ := phi_regular_from_slices f L μ hL hμ hdiffX hdiffY hsc hxx hxy
  have hE := saddleEnvelope_eq_moreau f L μ hμ hsc hdiffY
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [hE]
    exact MoreauTransfer.exact_stationarity_transfer (phi f) L hL hdiff hweak x
  · rw [hE]
    exact MoreauTransfer.initial_gap_transfer (phi f) L hL hdiff hweak hbelow x0 Δ hgap
  · rw [hE]
    exact MoreauTransfer.infimum_equality (phi f) L hL hdiff hweak hbelow
  · intro x
    have h := MoreauTransfer.exists_unique_minimizer (phi f) L hL hdiff hweak x
    simpa only [saddle_inner_value f L μ hμ hsc hdiffY] using h
  · intro x u
    simp only [saddle_inner_value f L μ hμ hsc hdiffY, uStar]
    exact MoreauTransfer.prox_minimizes (phi f) L hL hdiff hweak x u
  · intro x y
    exact add_le_add (yStar_maximizes f μ hμ hsc hdiffY (uStar f L x) y) (le_refl _)


theorem exact_transfer_from_standing_joint
    (J : JointSliceRegularity.JointSpace E F → ℝ)
    (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : JointSliceRegularity.JointSpace E F,
      ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hconcave : ∀ x : E, StrongConcaveOn (Set.univ : Set F) μ
      (fun y => J (WithLp.toLp 2 (x, y))))
    (hbelow : BddBelow (Set.range (phi (JointSliceRegularity.curry J))))
    (x0 : E) (Δ : ℝ)
    (hgap : phi (JointSliceRegularity.curry J) x0 -
      sInf (Set.range (phi (JointSliceRegularity.curry J))) ≤ Δ) :
    let f := JointSliceRegularity.curry J
    (∀ x : E,
      gradient (saddleEnvelope f L) x = (2 * L) • (x - uStar f L x) ∧
      gradient (saddleEnvelope f L) x = gradient (phi f) (uStar f L x)) ∧
    saddleEnvelope f L x0 - sInf (Set.range (saddleEnvelope f L)) ≤ Δ ∧
    sInf (Set.range (saddleEnvelope f L)) = sInf (Set.range (phi f)) ∧
    (∀ x : E, ∃! u : E, ∀ v : E,
      sSup (Set.range (saddleObjective f L x u)) ≤
      sSup (Set.range (saddleObjective f L x v))) ∧
    (∀ x : E, ∀ u : E,
      sSup (Set.range (saddleObjective f L x (uStar f L x))) ≤
      sSup (Set.range (saddleObjective f L x u))) ∧
    (∀ x : E, ∀ y : F,
      saddleObjective f L x (uStar f L x) y ≤
      saddleObjective f L x (uStar f L x) (vStar f L x)) := by
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hdiffX := JointSliceRegularity.differentiable_x_slice J hJ
  have hdiffY := JointSliceRegularity.differentiable_y_slice J hJ
  have hconcave' : ∀ x : E, StrongConcaveOn (Set.univ : Set F) μ
      (JointSliceRegularity.curry J x) := by
    intro x
    have heq : JointSliceRegularity.curry J x =
        (fun y : F => J (WithLp.toLp 2 (x, y))) := by
      funext y
      exact congrArg J (JointSliceRegularity.point_eq_toLp x y)
    rw [heq]
    exact hconcave x
  have hsc := JointSliceRegularity.strongConvex_negative_y_slice J μ hconcave'
  have hxx : ∀ y : F, ∀ x z : E,
      ‖gradient (fun t => JointSliceRegularity.curry J t y) x -
        gradient (fun t => JointSliceRegularity.curry J t y) z‖ ≤ L * ‖x - z‖ := by
    intro y x z
    exact JointSliceRegularity.gradient_x_lipschitz_in_x J hJ L hLip x z y
  have hxy : ∀ x : E, ∀ y z : F,
      ‖gradient (fun t => JointSliceRegularity.curry J t y) x -
        gradient (fun t => JointSliceRegularity.curry J t z) x‖ ≤ L * ‖y - z‖ := by
    intro x y z
    exact JointSliceRegularity.gradient_x_lipschitz_in_y J hJ L hLip x y z
  exact exact_transfer_from_slices (JointSliceRegularity.curry J) L μ hL hμ
    hdiffX hdiffY hsc hxx hxy hbelow x0 Δ hgap

end OriginalSaddleTransfer
end

section
-- Source component: SaddleStability.lean

namespace OriginalSaddleStability

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem norm_square_center_change (x u z : E) :
    ‖z - x‖ ^ 2 - ‖u - x‖ ^ 2 =
      ‖z - u‖ ^ 2 - 2 * inner ℝ (x - u) (z - u) := by
  simp only [norm_sub_sq_real, inner_sub_left, inner_sub_right,
    real_inner_self_eq_norm_sq]
  rw [real_inner_comm z x, real_inner_comm z u, real_inner_comm u x]
  ring

theorem norm_square_four_points (x x' u u' : E) :
    ‖u' - x‖ ^ 2 - ‖u - x‖ ^ 2 + ‖u - x'‖ ^ 2 - ‖u' - x'‖ ^ 2 =
      2 * inner ℝ (x - x') (u - u') := by
  simp only [norm_sub_sq_real, inner_sub_left, inner_sub_right]
  rw [real_inner_comm u' x, real_inner_comm u x,
    real_inner_comm u x', real_inner_comm u' x']
  ring

theorem fixed_dual_quadratic_growth
    (f : E → F → ℝ) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hdiffX : ∀ y : F, Differentiable ℝ (fun x => f x y))
    (hdiffY : ∀ x : E, Differentiable ℝ (f x))
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ (fun y => -f x y))
    (hxx : ∀ y : F, ∀ x z : E,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t y) z‖ ≤ L * ‖x - z‖)
    (hxy : ∀ x : E, ∀ y z : F,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t z) x‖ ≤ L * ‖y - z‖)
    (x z : E) :
    OriginalSaddleTransfer.saddleObjective f L x (OriginalSaddleTransfer.uStar f L x)
        (OriginalSaddleTransfer.vStar f L x) +
      L / 2 * ‖z - OriginalSaddleTransfer.uStar f L x‖ ^ 2 ≤
    OriginalSaddleTransfer.saddleObjective f L x z (OriginalSaddleTransfer.vStar f L x) := by
  let u := OriginalSaddleTransfer.uStar f L x
  let v := OriginalSaddleTransfer.vStar f L x
  obtain ⟨hphi, hweak⟩ := OriginalSaddleTransfer.phi_regular_from_slices
    f L μ hL hμ hdiffX hdiffY hsc hxx hxy
  have hFOC := MoreauTransfer.prox_first_order (OriginalSaddleTransfer.phi f) L
    hL hphi hweak x
  have hPhiGrad := (OriginalSaddleTransfer.phi_hasGradientAt_yStar f L μ hL hμ
    hdiffX hdiffY hsc hxx hxy u).gradient
  change gradient (OriginalSaddleTransfer.phi f) u = gradient (fun t => f t v) u at hPhiGrad
  have hgrad : gradient (fun t => f t v) u = (2 * L) • (x - u) := by
    exact hPhiGrad.symm.trans hFOC
  have hs := OriginalSaddleRegularity.smooth_gradient_lower_support
    (fun t => f t v) L hL (hdiffX v) (hxx v) u z
  rw [hgrad, real_inner_smul_left] at hs
  have heq := norm_square_center_change x u z
  have heqL := congrArg (fun t : ℝ => L * t) heq
  change f u v + L * ‖u - x‖ ^ 2 + L / 2 * ‖z - u‖ ^ 2 ≤
    f z v + L * ‖z - x‖ ^ 2
  nlinarith only [hs, heqL]

theorem actual_saddle_energy
    (f : E → F → ℝ) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hdiffX : ∀ y : F, Differentiable ℝ (fun x => f x y))
    (hdiffY : ∀ x : E, Differentiable ℝ (f x))
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ (fun y => -f x y))
    (hxx : ∀ y : F, ∀ x z : E,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t y) z‖ ≤ L * ‖x - z‖)
    (hxy : ∀ x : E, ∀ y z : F,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t z) x‖ ≤ L * ‖y - z‖)
    (x x' : E) :
    L * ‖OriginalSaddleTransfer.uStar f L x - OriginalSaddleTransfer.uStar f L x'‖ ^ 2 +
      μ * ‖OriginalSaddleTransfer.vStar f L x - OriginalSaddleTransfer.vStar f L x'‖ ^ 2 ≤
    2 * L * inner ℝ (x - x')
      (OriginalSaddleTransfer.uStar f L x - OriginalSaddleTransfer.uStar f L x') := by
  let u := OriginalSaddleTransfer.uStar f L x
  let u' := OriginalSaddleTransfer.uStar f L x'
  let v := OriginalSaddleTransfer.vStar f L x
  let v' := OriginalSaddleTransfer.vStar f L x'
  have hu := fixed_dual_quadratic_growth f L μ hL hμ hdiffX hdiffY hsc hxx hxy x u'
  have hu' := fixed_dual_quadratic_growth f L μ hL hμ hdiffX hdiffY hsc hxx hxy x' u
  have hv := OriginalSaddleRegularity.inner_maximum_quadratic_gap f μ hsc hdiffY
    (OriginalSaddleTransfer.yStar f)
    (OriginalSaddleTransfer.yStar_maximizes f μ hμ hsc hdiffY) u v'
  have hv' := OriginalSaddleRegularity.inner_maximum_quadratic_gap f μ hsc hdiffY
    (OriginalSaddleTransfer.yStar f)
    (OriginalSaddleTransfer.yStar_maximizes f μ hμ hsc hdiffY) u' v
  have hfour := norm_square_four_points x x' u u'
  have hfourL := congrArg (fun t : ℝ => L * t) hfour
  change L * ‖u - u'‖ ^ 2 + μ * ‖v - v'‖ ^ 2 ≤
    2 * L * inner ℝ (x - x') (u - u')
  change f u v + L * ‖u - x‖ ^ 2 + L / 2 * ‖u' - u‖ ^ 2 ≤
    f u' v + L * ‖u' - x‖ ^ 2 at hu
  change f u' v' + L * ‖u' - x'‖ ^ 2 + L / 2 * ‖u - u'‖ ^ 2 ≤
    f u v' + L * ‖u - x'‖ ^ 2 at hu'
  change f u v' ≤ f u v - μ / 2 * ‖v' - v‖ ^ 2 at hv
  change f u' v ≤ f u' v' - μ / 2 * ‖v - v'‖ ^ 2 at hv'
  rw [norm_sub_rev u' u] at hu
  rw [norm_sub_rev v' v] at hv
  nlinarith only [hu, hu', hv, hv', hfourL]

theorem scalar_energy_bounds
    (L μ a b c : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : L * a ^ 2 + μ * b ^ 2 ≤ 2 * L * c * a) :
    a ≤ 2 * c ∧ b ≤ 2 * Real.sqrt (L / μ) * c := by
  have ha' : a ≤ 2 * c := by
    by_contra hn
    have hp : 0 < a := by linarith
    have hb' : 0 ≤ μ * b ^ 2 := by positivity
    nlinarith only [h, hb', mul_pos hL hp, hn]
  refine ⟨ha', ?_⟩
  have hb' : μ * b ^ 2 ≤ 4 * L * c ^ 2 := by
    have h1 : 0 ≤ L * a ^ 2 := by positivity
    have h2 := mul_le_mul_of_nonneg_left ha' (by positivity : 0 ≤ 2 * L * c)
    nlinarith only [h, h1, h2]
  have hs : (Real.sqrt (L / μ)) ^ 2 = L / μ := Real.sq_sqrt (by positivity)
  have hμ0 : μ ≠ 0 := ne_of_gt hμ
  have hmul : μ * (L / μ) = L := by field_simp
  have hsquare : (2 * Real.sqrt (L / μ) * c) ^ 2 = 4 * (L / μ) * c ^ 2 := by
    rw [mul_pow, mul_pow, hs]
    ring
  have hsquare' : μ * (2 * Real.sqrt (L / μ) * c) ^ 2 = 4 * L * c ^ 2 := by
    rw [hsquare]
    nlinarith only [hmul]
  have hnonneg : 0 ≤ 2 * Real.sqrt (L / μ) * c := by positivity
  have hbb : b ^ 2 ≤ (2 * Real.sqrt (L / μ) * c) ^ 2 := by
    apply (mul_le_mul_iff_right₀ hμ).mp
    nlinarith only [hb', hsquare']
  exact (sq_le_sq₀ hb hnonneg).mp hbb

theorem actual_saddle_lipschitz_components
    (f : E → F → ℝ) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hdiffX : ∀ y : F, Differentiable ℝ (fun x => f x y))
    (hdiffY : ∀ x : E, Differentiable ℝ (f x))
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ (fun y => -f x y))
    (hxx : ∀ y : F, ∀ x z : E,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t y) z‖ ≤ L * ‖x - z‖)
    (hxy : ∀ x : E, ∀ y z : F,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t z) x‖ ≤ L * ‖y - z‖)
    (x x' : E) :
    ‖OriginalSaddleTransfer.uStar f L x - OriginalSaddleTransfer.uStar f L x'‖ ≤
      2 * ‖x - x'‖ ∧
    ‖OriginalSaddleTransfer.vStar f L x - OriginalSaddleTransfer.vStar f L x'‖ ≤
      2 * Real.sqrt (L / μ) * ‖x - x'‖ := by
  have he := actual_saddle_energy f L μ hL hμ hdiffX hdiffY hsc hxx hxy x x'
  have hi := real_inner_le_norm (x - x')
    (OriginalSaddleTransfer.uStar f L x - OriginalSaddleTransfer.uStar f L x')
  have hmul := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 2 * L)
  apply scalar_energy_bounds L μ _ _ _ hL hμ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
  exact he.trans (by nlinarith only [hmul])

noncomputable def zStar (f : E → F → ℝ) (L : ℝ) (x : E) : WithLp 2 (E × F) :=
  WithLp.toLp 2 (OriginalSaddleTransfer.uStar f L x, OriginalSaddleTransfer.vStar f L x)

theorem actual_saddle_lipschitz_joint
    (f : E → F → ℝ) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hdiffX : ∀ y : F, Differentiable ℝ (fun x => f x y))
    (hdiffY : ∀ x : E, Differentiable ℝ (f x))
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ (fun y => -f x y))
    (hxx : ∀ y : F, ∀ x z : E,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t y) z‖ ≤ L * ‖x - z‖)
    (hxy : ∀ x : E, ∀ y z : F,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t z) x‖ ≤ L * ‖y - z‖)
    (x x' : E) : ‖zStar f L x - zStar f L x'‖ ≤
      2 * Real.sqrt (1 + L / μ) * ‖x - x'‖ := by
  obtain ⟨hu, hv⟩ := actual_saddle_lipschitz_components f L μ hL hμ
    hdiffX hdiffY hsc hxx hxy x x'
  have hu2 := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2 * ‖x - x'‖)).mpr hu
  have hv2 := (sq_le_sq₀ (norm_nonneg _)
    (by positivity : 0 ≤ 2 * Real.sqrt (L / μ) * ‖x - x'‖)).mpr hv
  have hs := Real.sq_sqrt (by positivity : 0 ≤ L / μ)
  have hs1 := Real.sq_sqrt (by positivity : 0 ≤ 1 + L / μ)
  have hn := WithLp.prod_norm_sq_eq_of_L2 (zStar f L x - zStar f L x')
  change ‖zStar f L x - zStar f L x'‖ ^ 2 =
    ‖OriginalSaddleTransfer.uStar f L x - OriginalSaddleTransfer.uStar f L x'‖ ^ 2 +
    ‖OriginalSaddleTransfer.vStar f L x - OriginalSaddleTransfer.vStar f L x'‖ ^ 2 at hn
  apply (sq_le_sq₀ (norm_nonneg _)
    (by positivity : 0 ≤ 2 * Real.sqrt (1 + L / μ) * ‖x - x'‖)).mp
  have h0 : (2 * Real.sqrt (L / μ) * ‖x - x'‖) ^ 2 =
      4 * (L / μ) * ‖x - x'‖ ^ 2 := by
    rw [mul_pow, mul_pow, hs]
    ring
  have h1 : (2 * Real.sqrt (1 + L / μ) * ‖x - x'‖) ^ 2 =
      4 * (1 + L / μ) * ‖x - x'‖ ^ 2 := by
    rw [mul_pow, mul_pow, hs1]
    ring
  rw [h0] at hv2
  rw [h1]
  nlinarith only [hn, hu2, hv2]

theorem derivative_bounds_from_checked_differentials
    (f : E → F → ℝ) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hdiffX : ∀ y : F, Differentiable ℝ (fun x => f x y))
    (hdiffY : ∀ x : E, Differentiable ℝ (f x))
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ (fun y => -f x y))
    (hxx : ∀ y : F, ∀ x z : E,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t y) z‖ ≤ L * ‖x - z‖)
    (hxy : ∀ x : E, ∀ y z : F,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t z) x‖ ≤ L * ‖y - z‖)
    (x : E) (U : E →L[ℝ] E) (V : E →L[ℝ] F)
    (Z : E →L[ℝ] WithLp 2 (E × F))
    (hU : HasFDerivAt (OriginalSaddleTransfer.uStar f L) U x)
    (hV : HasFDerivAt (OriginalSaddleTransfer.vStar f L) V x)
    (hZ : HasFDerivAt (zStar f L) Z x) (h : E) :
    ‖U h‖ ≤ 2 * ‖h‖ ∧ ‖V h‖ ≤ 2 * Real.sqrt (L / μ) * ‖h‖ ∧
      ‖Z h‖ ≤ 2 * Real.sqrt (1 + L / μ) * ‖h‖ := by
  have hu : ‖U‖ ≤ 2 := hU.le_of_lip' (by norm_num)
    (Filter.Eventually.of_forall (fun z =>
      (actual_saddle_lipschitz_components f L μ hL hμ hdiffX hdiffY hsc hxx hxy z x).1))
  have hv : ‖V‖ ≤ 2 * Real.sqrt (L / μ) := hV.le_of_lip' (by positivity)
    (Filter.Eventually.of_forall (fun z =>
      (actual_saddle_lipschitz_components f L μ hL hμ hdiffX hdiffY hsc hxx hxy z x).2))
  have hz : ‖Z‖ ≤ 2 * Real.sqrt (1 + L / μ) := hZ.le_of_lip' (by positivity)
    (Filter.Eventually.of_forall (fun z =>
      actual_saddle_lipschitz_joint f L μ hL hμ hdiffX hdiffY hsc hxx hxy z x))
  exact ⟨(U.le_opNorm h).trans (mul_le_mul_of_nonneg_right hu (norm_nonneg h)),
    (V.le_opNorm h).trans (mul_le_mul_of_nonneg_right hv (norm_nonneg h)),
    (Z.le_opNorm h).trans (mul_le_mul_of_nonneg_right hz (norm_nonneg h))⟩

end OriginalSaddleStability
end
