import Bilevel.ZeroChainResidualJets

/-! The complete dimension-independent jet bound for the exact residual. -/

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Bilevel.ZeroChainResidualBounds
open ZeroChain ZeroChainProfiles ZeroChainPotential ZeroChainResidualCutoffs
  ZeroChainResidual ZeroChainResidualLocality ZeroChainResidualJets

theorem chain_profile_bound : ∃ K : ℝ, 1 ≤ K ∧ ∀ j : Fin 4, ∀ t,
    |iteratedDeriv j.val psi t| ≤ K ∧ |iteratedDeriv j.val phi t| ≤ K := by
  obtain ⟨A,hA,ha⟩ := psi_common_bound
  obtain ⟨B,hB,hb⟩ := phi_uniform_jet_bound
  refine ⟨A+B, by linarith, fun j t => ⟨?_, ?_⟩⟩
  · exact (ha j t).trans (le_add_of_nonneg_right hB.le)
  · exact (hb j t).trans (le_add_of_nonneg_left (by linarith))

theorem projection_norm_le {n : ℕ} (j : Fin (n+1)) : ‖EuclideanSpace.proj (𝕜:=ℝ) j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simpa only [one_mul] using PiLp.norm_apply_le z j

section JetHelpers
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem scalar_linear_jet_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (g : E →L[ℝ] ℝ) (hg : ‖g‖ ≤ 1) (x : E) (k : ℕ) (hk : k ≤ 3)
    (B : ℝ) (hB : 0 ≤ B) (hb : |iteratedDeriv k f (g x)| ≤ B) :
    ‖iteratedFDeriv ℝ k (f ∘ g) x‖ ≤ B := by
  rw [g.iteratedFDeriv_comp_right hf x (by exact_mod_cast hk)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  exact (mul_le_mul hb (pow_le_one₀ (norm_nonneg _) hg) (pow_nonneg (norm_nonneg _) _)
    hB).trans_eq (mul_one _)

theorem jet_sub_norm_le {f g : E → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    (x : E) (k : ℕ) (hk : k ≤ 3) :
    ‖iteratedFDeriv ℝ k (fun y => f y-g y) x‖ ≤
      ‖iteratedFDeriv ℝ k f x‖+‖iteratedFDeriv ℝ k g x‖ := by
  have hk' : (k : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hk
  simp only [sub_eq_add_neg]
  rw [iteratedFDeriv_add_apply' (hf.of_le hk').contDiffAt (hg.neg.of_le hk').contDiffAt]
  change ‖iteratedFDeriv ℝ k f x+iteratedFDeriv ℝ k (-g) x‖ ≤ _
  rw [iteratedFDeriv_neg_apply]
  simpa only [norm_neg] using norm_add_le (iteratedFDeriv ℝ k f x) (-iteratedFDeriv ℝ k g x)

theorem jet_mul_bound {f g : E → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    (x : E) (k : ℕ) (hk : k ≤ 3) (B C : ℕ → ℝ)
    (hB : ∀ j, 0 ≤ B j)
    (hb : ∀ j, j ≤ k → ‖iteratedFDeriv ℝ j f x‖ ≤ B j)
    (hc : ∀ j, j ≤ k → ‖iteratedFDeriv ℝ j g x‖ ≤ C j) :
    ‖iteratedFDeriv ℝ k (fun y => f y*g y) x‖ ≤
      ∑ j ∈ Finset.range (k+1), (k.choose j : ℝ)*B j*C (k-j) := by
  apply (norm_iteratedFDeriv_mul_le hf hg x (show (k:WithTop ℕ∞) ≤ 3 by exact_mod_cast hk)).trans
  apply Finset.sum_le_sum
  intro j hj
  have hjk : j ≤ k := by have hh := Finset.mem_range.mp hj; omega
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hb j hjk) (Nat.cast_nonneg _))
    (hc (k-j) (Nat.sub_le _ _)) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hB j))

theorem jet_mul_zero_left {f g : E → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    (x : E) (k : ℕ) (hk : k ≤ 3)
    (hf0 : ∀ j, j ≤ k → iteratedFDeriv ℝ j f x = 0) :
    iteratedFDeriv ℝ k (fun y => f y*g y) x = 0 := by
  have hb := norm_iteratedFDeriv_mul_le hf hg x (show (k:WithTop ℕ∞) ≤ 3 by exact_mod_cast hk)
  have hs : (∑ j ∈ Finset.range (k+1), (k.choose j : ℝ)*‖iteratedFDeriv ℝ j f x‖*
      ‖iteratedFDeriv ℝ (k-j) g x‖) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hf0 j (by have := Finset.mem_range.mp hj; omega), norm_zero, mul_zero, zero_mul]
  rw [hs] at hb
  exact norm_le_zero_iff.mp hb

theorem jet_mul_zero_right {f g : E → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    (x : E) (k : ℕ) (hk : k ≤ 3)
    (hg0 : ∀ j, j ≤ k → iteratedFDeriv ℝ j g x = 0) :
    iteratedFDeriv ℝ k (fun y => f y*g y) x = 0 := by
  have he : (fun y => f y*g y) = fun y => g y*f y := by ext y; ring
  rw [he]
  exact jet_mul_zero_left hg hf x k hk hg0

end JetHelpers

def componentJetBound (K : ℝ) (k : ℕ) : ℝ :=
  K+2*∑ j ∈ Finset.range (k+1), (k.choose j : ℝ)*K*K

theorem componentJetBound_nonneg {K : ℝ} (hK : 0 ≤ K) (k : ℕ) : 0 ≤ componentJetBound K k := by
  dsimp [componentJetBound]
  positivity

theorem component_jet_bound {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ j : Fin 4, ∀ t, |iteratedDeriv j.val psi t| ≤ K ∧ |iteratedDeriv j.val phi t| ≤ K)
    (n : ℕ) (i : Fin (n+1)) (z : Space n) (k : ℕ) (hk : k ≤ 3) :
    ‖iteratedFDeriv ℝ k (component n i) z‖ ≤ componentJetBound K k := by
  have hψ (g : Space n →L[ℝ] ℝ) (hg : ‖g‖ ≤ 1) (j : ℕ) (hj : j ≤ k) :
      ‖iteratedFDeriv ℝ j (psi ∘ g) z‖ ≤ K :=
    scalar_linear_jet_bound (psi_contDiff (n:=3)) g hg z j (by omega) K hK (hb ⟨j,by omega⟩ _).1
  have hφ (g : Space n →L[ℝ] ℝ) (hg : ‖g‖ ≤ 1) (j : ℕ) (hj : j ≤ k) :
      ‖iteratedFDeriv ℝ j (phi ∘ g) z‖ ≤ K :=
    scalar_linear_jet_bound (phi_contDiff 3) g hg z j (by omega) K hK (hb ⟨j,by omega⟩ _).2
  have hs : 0 ≤ ∑ j ∈ Finset.range (k+1), (k.choose j : ℝ)*K*K := by positivity
  refine Fin.cases ?_ (fun l => ?_) i
  · change ‖iteratedFDeriv ℝ k (-(phi ∘ EuclideanSpace.proj (𝕜:=ℝ) (0:Fin (n+1)))) z‖ ≤ _
    rw [iteratedFDeriv_neg_apply, norm_neg]
    exact (hφ _ (projection_norm_le _) k le_rfl).trans (by dsimp [componentJetBound]; linarith)
  · let p := EuclideanSpace.proj (𝕜:=ℝ) l.castSucc
    let q := EuclideanSpace.proj (𝕜:=ℝ) l.succ
    have hp : ‖p‖ ≤ 1 := projection_norm_le _
    have hq : ‖q‖ ≤ 1 := projection_norm_le _
    have hmp : ‖-p‖ ≤ 1 := by simpa only [norm_neg] using hp
    have hmq : ‖-q‖ ≤ 1 := by simpa only [norm_neg] using hq
    have hmn := jet_mul_bound ((psi_contDiff (n:=3)).comp (-p).contDiff)
      ((phi_contDiff 3).comp (-q).contDiff) z k hk (fun _ => K) (fun _ => K)
      (fun _ => hK) (hψ (-p) hmp) (hφ (-q) hmq)
    have hpl := jet_mul_bound ((psi_contDiff (n:=3)).comp p.contDiff)
      ((phi_contDiff 3).comp q.contDiff) z k hk (fun _ => K) (fun _ => K)
      (fun _ => hK) (hψ p hp) (hφ q hq)
    have ht := jet_sub_norm_le
      (((psi_contDiff (n:=3)).comp (-p).contDiff).mul ((phi_contDiff 3).comp (-q).contDiff))
      (((psi_contDiff (n:=3)).comp p.contDiff).mul ((phi_contDiff 3).comp q.contDiff)) z k hk
    dsimp only [Function.comp_apply, ContinuousLinearMap.neg_apply] at hmn hpl ht
    change ‖iteratedFDeriv ℝ k (fun w => psi (-p w)*phi (-q w)-psi (p w)*phi (q w)) z‖ ≤ _
    exact ht.trans (by dsimp [componentJetBound]; linarith)

theorem component_succ_flat_jet {n : ℕ} (i : Fin n) (z : Space n)
    (hz : |z i.castSucc| ≤ 1/2) (k : ℕ) (hk : k ≤ 3) :
    iteratedFDeriv ℝ k (component n i.succ) z = 0 := by
  let p := EuclideanSpace.proj (𝕜:=ℝ) i.castSucc
  let q := EuclideanSpace.proj (𝕜:=ℝ) i.succ
  have hp : ‖p‖ ≤ 1 := projection_norm_le _
  have hmp : ‖-p‖ ≤ 1 := by simpa only [norm_neg] using hp
  have hpz : p z ≤ 1/2 := (abs_le.mp hz).2
  have hmpz : (-p) z ≤ 1/2 := by
    change -z i.castSucc ≤ 1/2
    linarith [(abs_le.mp hz).1]
  have hf (g : Space n →L[ℝ] ℝ) (hg : ‖g‖ ≤ 1) (hgz : g z ≤ 1/2)
      (j : ℕ) (hj : j ≤ k) : iteratedFDeriv ℝ j (psi ∘ g) z = 0 := by
    apply norm_le_zero_iff.mp
    apply scalar_linear_jet_bound (psi_contDiff (n:=3)) g hg z j (by omega) 0 le_rfl
    rw [psi_iteratedDeriv_zero_of_le j hgz, abs_zero]
  have hm := jet_mul_zero_left ((psi_contDiff (n:=3)).comp (-p).contDiff)
    ((phi_contDiff 3).comp (-q).contDiff) z k hk (hf (-p) hmp hmpz)
  have hpl := jet_mul_zero_left ((psi_contDiff (n:=3)).comp p.contDiff)
    ((phi_contDiff 3).comp q.contDiff) z k hk (hf p hp hpz)
  have ht := jet_sub_norm_le
    (((psi_contDiff (n:=3)).comp (-p).contDiff).mul ((phi_contDiff 3).comp (-q).contDiff))
    (((psi_contDiff (n:=3)).comp p.contDiff).mul ((phi_contDiff 3).comp q.contDiff)) z k hk
  rw [hm, hpl, norm_zero, zero_add] at ht
  exact norm_le_zero_iff.mp ht

theorem masked_jet_flat_small_predecessor {n : ℕ} (i : Fin n) (z : Space n)
    (hz : |z i.castSucc| ≤ 1/2) (k : ℕ) (hk : k ≤ 3) :
    iteratedFDeriv ℝ k (maskedComponent i.succ) z = 0 :=
  jet_mul_zero_left (component_contDiff n i.succ) (tailMask_contDiff i.succ) z k hk
    (fun j hj => component_succ_flat_jet i z hz j (by omega))

theorem masked_jet_flat_large_tail {n : ℕ} (i j : Fin (n+1)) (z : Space n)
    (hij : i ≤ j) (hz : 1/2 ≤ |z j|) (k : ℕ) (hk : k ≤ 3) :
    iteratedFDeriv ℝ k (maskedComponent i) z = 0 := by
  have he : 1 ≤ tailEnergy i z := by
    have hh := coordinate_energy_le i j z hij
    simpa only [coordinateCutoff_one hz, one_pow] using hh
  exact jet_mul_zero_right (component_contDiff n i) (tailMask_contDiff i) z k hk
    (fun l hl => tailMask_flat_jet i z he l (by omega))

theorem jet_before_nonzero_later {n : ℕ} (i j : Fin (n+1)) (z : Space n)
    (k : ℕ) (hk : k ≤ 3) (hij : i < j)
    (hj : iteratedFDeriv ℝ k (maskedComponent j) z ≠ 0) :
    iteratedFDeriv ℝ k (maskedComponent i) z = 0 := by
  revert hij hj
  refine Fin.cases ?_ (fun l => ?_) j
  · intro hij _
    exact (Fin.not_lt_zero i hij).elim
  · intro hij hj
    have hl : 1/2 < |z l.castSucc| := by
      by_contra! hh
      exact hj (masked_jet_flat_small_predecessor l z hh k hk)
    apply masked_jet_flat_large_tail i l.castSucc z ?_ hl.le k hk
    change i.val ≤ l.val
    have hh : i.val < l.val+1 := hij
    omega

/-- The single-active-term property holds for every actual jet through order
three, including the boundaries of the cutoffs. -/
theorem masked_jets_exclusive {n : ℕ} (z : Space n) (k : ℕ) (hk : k ≤ 3)
    (i j : Fin (n+1)) (hij : i ≠ j)
    (hi : iteratedFDeriv ℝ k (maskedComponent i) z ≠ 0) :
    iteratedFDeriv ℝ k (maskedComponent j) z = 0 := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · by_contra hj
    exact hi (jet_before_nonzero_later i j z k hk hlt hj)
  · exact jet_before_nonzero_later j i z k hk hgt hi

def maskJetBound (C : ℝ) (k : ℕ) : ℝ := (k.factorial:ℝ)*C*(2*C)^k
def residualJetBound (K C : ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k+1), (k.choose j:ℝ)*componentJetBound K j*maskJetBound C (k-j)

theorem maskJetBound_nonneg {C : ℝ} (hC : 0 ≤ C) (k : ℕ) : 0 ≤ maskJetBound C k := by
  dsimp [maskJetBound]
  positivity

theorem residualJetBound_nonneg {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (k : ℕ) :
    0 ≤ residualJetBound K C k := by
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (componentJetBound_nonneg hK j))
    (maskJetBound_nonneg hC _)

theorem maskedComponent_jet_bound {K C : ℝ} (hK : 0 ≤ K) (hC : MaskControl C)
    (hb : ∀ j : Fin 4, ∀ t, |iteratedDeriv j.val psi t| ≤ K ∧ |iteratedDeriv j.val phi t| ≤ K)
    {n : ℕ} (i : Fin (n+1)) (z : Space n) (k : ℕ) (hk : k ≤ 3) :
    ‖iteratedFDeriv ℝ k (maskedComponent i) z‖ ≤ residualJetBound K C k :=
  jet_mul_bound (component_contDiff n i) (tailMask_contDiff i) z k hk
    (componentJetBound K) (maskJetBound C) (componentJetBound_nonneg hK)
    (fun j hj => component_jet_bound hK hb n i z j (by omega))
    (fun j hj => tailMask_jet_bound hC i z j (by omega))

theorem norm_sum_le_of_exclusive {ι F : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup F]
    (f : ι → F) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ i, ‖f i‖ ≤ B)
    (he : ∀ i j, i ≠ j → f i ≠ 0 → f j = 0) : ‖∑ i, f i‖ ≤ B := by
  by_cases hf : ∃ i, f i ≠ 0
  · obtain ⟨i,hi⟩ := hf
    rw [Finset.sum_eq_single i]
    · exact hb i
    · intro j _ hji
      exact he i j hji.symm hi
    · simp
  · have hz : ∀ i, f i = 0 := by simpa only [not_exists, not_not] using hf
    simp only [hz, Finset.sum_const_zero, norm_zero]
    exact hB

theorem rawResidual_jet_bound {K C : ℝ} (hK : 0 ≤ K) (hC : MaskControl C)
    (hb : ∀ j : Fin 4, ∀ t, |iteratedDeriv j.val psi t| ≤ K ∧ |iteratedDeriv j.val phi t| ≤ K)
    (n : ℕ) (z : Space n) (k : ℕ) (hk : k ≤ 3) :
    ‖iteratedFDeriv ℝ k (rawResidual n) z‖ ≤ residualJetBound K C k := by
  change ‖iteratedFDeriv ℝ k (fun w => ∑ i : Fin (n+1), maskedComponent i w) z‖ ≤ _
  rw [iteratedFDeriv_sum (fun i _ => (maskedComponent_contDiff i).of_le
    (show (k:WithTop ℕ∞) ≤ 3 by exact_mod_cast hk))]
  simp only [Finset.sum_apply]
  exact norm_sum_le_of_exclusive _ _ (residualJetBound_nonneg hK (by linarith [hC.one_le]) k)
    (fun i => maskedComponent_jet_bound hK hC hb i z k hk) (masked_jets_exclusive z k hk)

theorem residual_jet_bound {K C : ℝ} (hK : 0 ≤ K) (hC : MaskControl C)
    (hb : ∀ j : Fin 4, ∀ t, |iteratedDeriv j.val psi t| ≤ K ∧ |iteratedDeriv j.val phi t| ≤ K)
    (n : ℕ) (z : Space n) (k : ℕ) (hk : k ≤ 3) :
    ‖iteratedFDeriv ℝ k (residual n) z‖ ≤ 2*residualJetBound K C k := by
  have hr := rawResidual_jet_bound hK hC hb n z k hk
  have ht := jet_sub_norm_le (rawResidual_contDiff n) (contDiff_const (c:=rawResidual n 0)) z k hk
  by_cases hk0 : k = 0
  · subst k
    have hzero := rawResidual_jet_bound hK hC hb n 0 0 (by norm_num)
    simp only [norm_iteratedFDeriv_zero] at hr ht hzero ⊢
    exact ht.trans (by linarith)
  · rw [iteratedFDeriv_const_of_ne hk0, Pi.zero_apply, norm_zero, add_zero] at ht
    have hnonneg := residualJetBound_nonneg (C:=C) hK (by linarith [hC.one_le]) k
    exact ht.trans (hr.trans (by linarith))

/-- The original residual certificate at unit amplitude and unit scale.
Each constant is numerical and independent of the chain length. -/
theorem residual_uniform_jet_bound : ∃ B : Fin 4 → ℝ, (∀ j, 0 ≤ B j) ∧
    ∀ (j : Fin 4) (n : ℕ) (z : Space n), ‖iteratedFDeriv ℝ j.val (residual n) z‖ ≤ B j := by
  obtain ⟨K,hK,hb⟩ := chain_profile_bound
  obtain ⟨C,hC⟩ := mask_control_exists
  refine ⟨fun j => 2*residualJetBound K C j.val, fun j => ?_, fun j n z => ?_⟩
  · exact mul_nonneg (by norm_num) (residualJetBound_nonneg (by linarith) (by linarith [hC.one_le]) _)
  · exact residual_jet_bound (by linarith) hC hb n z j.val (by omega)

end Bilevel.ZeroChainResidualBounds
