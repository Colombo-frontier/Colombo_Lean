import Bilevel.ZeroChainChildProfiles

/-! Exact annular localization of the jets of two flattening resolutions. -/

noncomputable section
open Set
open scoped BigOperators RealInnerProductSpace

namespace Bilevel.ZeroChainFlatteningAnnulus
open ZeroChain ZeroChainProfiles ZeroChainPotential ZeroChainResidualCutoffs ZeroChainResidual
  ZeroChainResidualBounds ZeroChainResidualJets ZeroChainFlatteningCutoff ZeroChainFlatteningMap
  ZeroChainChildProfiles

theorem scalar_coordinate_jet_zero {n : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (i : Fin (n+1)) (z : Space n) (k : ℕ) (hk : k ≤ 3) (hz : iteratedDeriv k f (z i) = 0) :
    iteratedFDeriv ℝ k (f ∘ EuclideanSpace.proj (𝕜:=ℝ) i) z = 0 := by
  apply norm_le_zero_iff.mp
  exact scalar_linear_jet_bound hf _ (projection_norm_le i) z k hk 0 le_rfl (by
    change |iteratedDeriv k f (z i)| ≤ 0
    rw [hz, abs_zero])

theorem childComponent_flat_parent {n : ℕ} {p m : ℝ → ℝ} (hp : ContDiff ℝ 3 p) (hm : ContDiff ℝ 3 m)
    (i : Fin n) (z : Space n) (hz : |z i.castSucc| ≤ 1/2) (k : ℕ) (hk : k ≤ 3) :
    iteratedFDeriv ℝ k (childComponent n p m i.succ) z = 0 := by
  let u := EuclideanSpace.proj (𝕜:=ℝ) i.castSucc
  let v := EuclideanSpace.proj (𝕜:=ℝ) i.succ
  have hu : ‖u‖ ≤ 1 := projection_norm_le _
  have hmu : ‖-u‖ ≤ 1 := by simpa only [norm_neg] using hu
  have hu0 : u z ≤ 1/2 := (abs_le.mp hz).2
  have hmu0 : (-u) z ≤ 1/2 := by change -z i.castSucc ≤ 1/2; linarith [(abs_le.mp hz).1]
  have hg (g : Space n →L[ℝ] ℝ) (hgn : ‖g‖ ≤ 1) (hgz : g z ≤ 1/2)
      (j : ℕ) (hj : j ≤ k) : iteratedFDeriv ℝ j (psi ∘ g) z = 0 := by
    apply norm_le_zero_iff.mp
    apply scalar_linear_jet_bound (psi_contDiff (n:=3)) g hgn z j (by omega) 0 le_rfl
    rw [psi_iteratedDeriv_zero_of_le j hgz, abs_zero]
  have hleft := jet_mul_zero_left ((psi_contDiff (n:=3)).comp (-u).contDiff) (hm.comp v.contDiff)
    z k hk (hg (-u) hmu hmu0)
  have hright := jet_mul_zero_left ((psi_contDiff (n:=3)).comp u.contDiff) (hp.comp v.contDiff)
    z k hk (hg u hu hu0)
  have ht := jet_sub_norm_le
    (((psi_contDiff (n:=3)).comp (-u).contDiff).mul (hm.comp v.contDiff))
    (((psi_contDiff (n:=3)).comp u.contDiff).mul (hp.comp v.contDiff)) z k hk
  rw [hleft, hright, norm_zero, zero_add] at ht
  exact norm_le_zero_iff.mp ht

theorem childComponent_flat_child {n : ℕ} {p m : ℝ → ℝ} (hp : ContDiff ℝ 3 p) (hm : ContDiff ℝ 3 m)
    (i : Fin (n+1)) (z : Space n) (k : ℕ) (hk : k ≤ 3)
    (hp0 : ∀ j, j ≤ k → iteratedDeriv j p (z i) = 0)
    (hm0 : ∀ j, j ≤ k → iteratedDeriv j m (z i) = 0) :
    iteratedFDeriv ℝ k (childComponent n p m i) z = 0 := by
  revert hp0 hm0
  refine Fin.cases ?_ (fun l => ?_) i
  · intro hp0 _
    change iteratedFDeriv ℝ k (-(p ∘ EuclideanSpace.proj (𝕜:=ℝ) (0:Fin (n+1)))) z = 0
    rw [iteratedFDeriv_neg_apply, scalar_coordinate_jet_zero hp 0 z k hk (hp0 k le_rfl), neg_zero]
  · intro hp0 hm0
    let u := EuclideanSpace.proj (𝕜:=ℝ) l.castSucc
    let v := EuclideanSpace.proj (𝕜:=ℝ) l.succ
    have hleft := jet_mul_zero_right ((psi_contDiff (n:=3)).comp (-u).contDiff) (hm.comp v.contDiff)
      z k hk (fun j hj => scalar_coordinate_jet_zero hm l.succ z j (by omega) (hm0 j hj))
    have hright := jet_mul_zero_right ((psi_contDiff (n:=3)).comp u.contDiff) (hp.comp v.contDiff)
      z k hk (fun j hj => scalar_coordinate_jet_zero hp l.succ z j (by omega) (hp0 j hj))
    have ht := jet_sub_norm_le
      (((psi_contDiff (n:=3)).comp (-u).contDiff).mul (hm.comp v.contDiff))
      (((psi_contDiff (n:=3)).comp u.contDiff).mul (hp.comp v.contDiff)) z k hk
    rw [hleft, hright, norm_zero, zero_add] at ht
    exact norm_le_zero_iff.mp ht

theorem maskedChild_flat_parent {n : ℕ} {p m : ℝ → ℝ} (hp : ContDiff ℝ 3 p) (hm : ContDiff ℝ 3 m)
    (i : Fin n) (z : Space n) (hz : |z i.castSucc| ≤ 1/2) (k : ℕ) (hk : k ≤ 3) :
    iteratedFDeriv ℝ k (maskedChild p m i.succ) z = 0 :=
  jet_mul_zero_left (childComponent_contDiff n hp hm i.succ) (tailMask_contDiff i.succ) z k hk
    (fun j hj => childComponent_flat_parent hp hm i z hz j (by omega))

theorem maskedChild_flat_child {n : ℕ} {p m : ℝ → ℝ} (hp : ContDiff ℝ 3 p) (hm : ContDiff ℝ 3 m)
    (i : Fin (n+1)) (z : Space n) (k : ℕ) (hk : k ≤ 3)
    (hp0 : ∀ j, j ≤ k → iteratedDeriv j p (z i) = 0)
    (hm0 : ∀ j, j ≤ k → iteratedDeriv j m (z i) = 0) :
    iteratedFDeriv ℝ k (maskedChild p m i) z = 0 :=
  jet_mul_zero_left (childComponent_contDiff n hp hm i) (tailMask_contDiff i) z k hk
    (fun j hj => childComponent_flat_child hp hm i z j (by omega)
      (fun l hl => hp0 l (by omega)) (fun l hl => hm0 l (by omega)))

theorem maskedChild_flat_tail {n : ℕ} {p m : ℝ → ℝ} (hp : ContDiff ℝ 3 p) (hm : ContDiff ℝ 3 m)
    (i j : Fin (n+1)) (z : Space n) (hij : i ≤ j) (hz : 1/2 ≤ |z j|) (k : ℕ) (hk : k ≤ 3) :
    iteratedFDeriv ℝ k (maskedChild p m i) z = 0 := by
  have he : 1 ≤ tailEnergy i z := by
    have hh := coordinate_energy_le i j z hij
    simpa only [coordinateCutoff_one hz, one_pow] using hh
  exact jet_mul_zero_right (childComponent_contDiff n hp hm i) (tailMask_contDiff i) z k hk
    (fun l hl => tailMask_flat_jet i z he l (by omega))

theorem maskedChild_jet_before_later {n : ℕ} {p m p' m' : ℝ → ℝ}
    (hp : ContDiff ℝ 3 p) (hm : ContDiff ℝ 3 m) (hp' : ContDiff ℝ 3 p') (hm' : ContDiff ℝ 3 m')
    (z : Space n) (i j : Fin (n+1)) (hij : i < j) (k l : ℕ) (hk : k ≤ 3) (hl : l ≤ 3)
    (hj : iteratedFDeriv ℝ l (maskedChild p' m' j) z ≠ 0) :
    iteratedFDeriv ℝ k (maskedChild p m i) z = 0 := by
  revert hij hj
  refine Fin.cases ?_ (fun s => ?_) j
  · intro hij _
    exact (Fin.not_lt_zero i hij).elim
  · intro hij hj
    have hs : 1/2 < |z s.castSucc| := by
      by_contra! hs
      exact hj (maskedChild_flat_parent hp' hm' s z hs l hl)
    apply maskedChild_flat_tail hp hm i s.castSucc z ?_ hs.le k hk
    change i.val ≤ s.val
    have h : i.val < s.val+1 := hij
    omega

/-- The active chain coordinate is common to every smooth choice of child
profiles and every derivative order through three. -/
theorem maskedChild_cross_jet_exclusive {n : ℕ} {p m p' m' : ℝ → ℝ}
    (hp : ContDiff ℝ 3 p) (hm : ContDiff ℝ 3 m) (hp' : ContDiff ℝ 3 p') (hm' : ContDiff ℝ 3 m')
    (z : Space n) (i j : Fin (n+1)) (hij : i ≠ j) (k l : ℕ) (hk : k ≤ 3) (hl : l ≤ 3)
    (hi : iteratedFDeriv ℝ k (maskedChild p m i) z ≠ 0) :
    iteratedFDeriv ℝ l (maskedChild p' m' j) z = 0 := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · by_contra hj
    exact hi (maskedChild_jet_before_later hp hm hp' hm' z i j hlt k l hk hl hj)
  · exact maskedChild_jet_before_later hp' hm' hp hm z j i hgt l k hl hk hi

def resolutionDifference (s δ' δ t : ℝ) : ℝ :=
  phi (s*flatten δ' t)-phi (s*flatten δ t)

theorem resolutionDifference_contDiff (s δ' δ : ℝ) : ContDiff ℝ 3 (resolutionDifference s δ' δ) :=
  ((phi_contDiff 3).comp (contDiff_const.mul (flatten_contDiff δ'))).sub
    ((phi_contDiff 3).comp (contDiff_const.mul (flatten_contDiff δ)))

theorem resolutionDifference_zero_inner (s : ℝ) {δ' δ t : ℝ}
    (hδ' : 0 < δ') (hδ : δ' ≤ δ) (ht : |t| ≤ δ') : resolutionDifference s δ' δ t = 0 := by
  rw [resolutionDifference, flatten_zero hδ' ht, flatten_zero (lt_of_lt_of_le hδ' hδ) (ht.trans hδ), sub_self]

theorem resolutionDifference_zero_outer (s : ℝ) {δ' δ t : ℝ}
    (hδ' : 0 < δ') (hδ : δ' ≤ δ) (ht : 2*δ ≤ |t|) : resolutionDifference s δ' δ t = 0 := by
  rw [resolutionDifference, flatten_identity hδ' (by linarith),
    flatten_identity (lt_of_lt_of_le hδ' hδ) ht, sub_self]

theorem resolutionDifference_flat (s : ℝ) {δ' δ : ℝ} (hδ' : 0 < δ') (hδ : δ' ≤ δ)
    (k : ℕ) (hk : k ≤ 3) (t : ℝ) (ht : ¬(δ' < |t| ∧ |t| < 2*δ)) :
    iteratedDeriv k (resolutionDifference s δ' δ) t = 0 := by
  have he (u : ℝ) (hu : |u| ≤ δ') := resolutionDifference_zero_inner s hδ' hδ hu
  have ho (u : ℝ) (hu : 2*δ ≤ |u|) := resolutionDifference_zero_outer s hδ' hδ hu
  by_cases hk0 : k = 0
  · subst k
    simp only [iteratedDeriv_zero]
    by_cases hsmall : |t| ≤ δ'
    · exact he t hsmall
    · exact ho t (by by_contra! hh; exact ht ⟨lt_of_not_ge hsmall,hh⟩)
  · by_cases hsmall : |t| ≤ δ'
    · exact iteratedDeriv_zero_of_constant_on (resolutionDifference_contDiff s δ' δ)
        (uniqueDiffOn_Icc (show -δ' < δ' by linarith)) (fun u hu => he u (abs_le.mpr hu))
        k (by omega) hk t (abs_le.mp hsmall)
    · have hout : 2*δ ≤ |t| := by by_contra! hh; exact ht ⟨lt_of_not_ge hsmall,hh⟩
      rcases le_total 0 t with hp | hn
      · apply iteratedDeriv_zero_of_constant_on (resolutionDifference_contDiff s δ' δ)
          (uniqueDiffOn_Ici (2*δ)) (fun u hu => ho u (by
            change 2*δ ≤ u at hu
            rw [abs_of_nonneg (by linarith : 0 ≤ u)]
            exact hu)) k (by omega) hk t
        simpa only [abs_of_nonneg hp] using hout
      · apply iteratedDeriv_zero_of_constant_on (resolutionDifference_contDiff s δ' δ)
          (uniqueDiffOn_Iic (-(2*δ))) (fun u hu => ho u (by
            change u ≤ -(2*δ) at hu
            rw [abs_of_nonpos (by linarith : u ≤ 0)]
            linarith)) k (by omega) hk t
        change t ≤ -(2*δ)
        rw [abs_of_nonpos hn] at hout
        linarith

def differenceTerm {n : ℕ} (δ' δ : ℝ) (i : Fin (n+1)) : Space n → ℝ :=
  maskedChild (resolutionDifference 1 δ' δ) (resolutionDifference (-1) δ' δ) i

def differenceRaw (n : ℕ) (δ' δ : ℝ) : Space n → ℝ :=
  rawChild n (resolutionDifference 1 δ' δ) (resolutionDifference (-1) δ' δ)

theorem differenceTerm_contDiff {n : ℕ} (δ' δ : ℝ) (i : Fin (n+1)) :
    ContDiff ℝ 3 (differenceTerm δ' δ i) :=
  maskedChild_contDiff (resolutionDifference_contDiff 1 δ' δ) (resolutionDifference_contDiff (-1) δ' δ) i

theorem differenceRaw_contDiff (n : ℕ) (δ' δ : ℝ) : ContDiff ℝ 3 (differenceRaw n δ' δ) :=
  rawChild_contDiff n (resolutionDifference_contDiff 1 δ' δ) (resolutionDifference_contDiff (-1) δ' δ)

theorem normalized_difference_eq {δ' δ : ℝ} (hδ' : 0 < δ') (hδ : δ' ≤ δ) (hsmall : δ ≤ 1/16)
    (n : ℕ) :
    (fun z => ZeroChainResidual.residual n (flattenMap n δ' z)-ZeroChainResidual.residual n (flattenMap n δ z)) =
      differenceRaw n δ' δ := by
  ext z
  calc
    _ = rawResidual n (flattenMap n δ' z)-rawResidual n (flattenMap n δ z) := by
      dsimp [ZeroChainResidual.residual]
      ring
    _ = rawChild n (fun t => phi (flatten δ' t)) (fun t => phi (-flatten δ' t)) z-
        rawChild n (fun t => phi (flatten δ t)) (fun t => phi (-flatten δ t)) z := by
      rw [rawResidual_flattenMap_eq hδ' (hδ.trans hsmall),
        rawResidual_flattenMap_eq (lt_of_lt_of_le hδ' hδ) hsmall]
    _ = _ := by
      rw [rawChild_sub]
      simp only [differenceRaw, resolutionDifference, one_mul, neg_one_mul]
      congr 2 <;> ext t <;> simp [resolutionDifference]

theorem differenceTerm_flat_outside_annulus {n : ℕ} {δ' δ : ℝ} (hδ' : 0 < δ') (hδ : δ' ≤ δ)
    (i : Fin (n+1)) (z : Space n) (k : ℕ) (hk : k ≤ 3)
    (hi : ¬(δ' < |z i| ∧ |z i| < 2*δ)) : iteratedFDeriv ℝ k (differenceTerm δ' δ i) z = 0 :=
  maskedChild_flat_child (resolutionDifference_contDiff 1 δ' δ) (resolutionDifference_contDiff (-1) δ' δ)
    i z k hk (fun j hj => resolutionDifference_flat 1 hδ' hδ j (by omega) _ hi)
    (fun j hj => resolutionDifference_flat (-1) hδ' hδ j (by omega) _ hi)

theorem differenceRaw_jet_sum (n : ℕ) (δ' δ : ℝ) (z : Space n) (k : ℕ) (hk : k ≤ 3) :
    iteratedFDeriv ℝ k (differenceRaw n δ' δ) z =
      ∑ i : Fin (n+1), iteratedFDeriv ℝ k (differenceTerm δ' δ i) z := by
  change iteratedFDeriv ℝ k (fun w => ∑ i : Fin (n+1), differenceTerm δ' δ i w) z = _
  rw [iteratedFDeriv_sum (fun i _ => (differenceTerm_contDiff δ' δ i).of_le
    (show (k:WithTop ℕ∞) ≤ 3 by exact_mod_cast hk))]
  simp only [Finset.sum_apply]

theorem differenceRaw_jet_nonzero_term (n : ℕ) (δ' δ : ℝ) (z : Space n) (k : ℕ) (hk : k ≤ 3)
    (h : iteratedFDeriv ℝ k (differenceRaw n δ' δ) z ≠ 0) :
    ∃ i : Fin (n+1), iteratedFDeriv ℝ k (differenceTerm δ' δ i) z ≠ 0 := by
  classical
  by_contra! he
  apply h
  rw [differenceRaw_jet_sum n δ' δ z k hk]
  exact Finset.sum_eq_zero (fun i _ => he i)

/-- A nonzero jet at either resolution has a unique common active child,
which must lie in the stated strict annulus. Every other child jet vanishes
through order three, even for any other smooth resolution profiles. -/
theorem nonzero_difference_jet_annulus {δ' δ : ℝ} (hδ' : 0 < δ') (hδ : δ' ≤ δ)
    (n : ℕ) (z : Space n) (k : ℕ) (hk : k ≤ 3)
    (h : iteratedFDeriv ℝ k (differenceRaw n δ' δ) z ≠ 0) :
    ∃ i : Fin (n+1), (δ' < |z i| ∧ |z i| < 2*δ) ∧
      iteratedFDeriv ℝ k (differenceTerm δ' δ i) z ≠ 0 ∧
      ∀ (p m : ℝ → ℝ), ContDiff ℝ 3 p → ContDiff ℝ 3 m → ∀ j : Fin (n+1), i ≠ j →
        ∀ l : ℕ, l ≤ 3 → iteratedFDeriv ℝ l (maskedChild p m j) z = 0 := by
  obtain ⟨i,hi⟩ := differenceRaw_jet_nonzero_term n δ' δ z k hk h
  refine ⟨i, ?_, hi, ?_⟩
  · by_contra hn
    exact hi (differenceTerm_flat_outside_annulus hδ' hδ i z k hk hn)
  · intro p m hp hm j hij l hl
    exact maskedChild_cross_jet_exclusive (resolutionDifference_contDiff 1 δ' δ)
      (resolutionDifference_contDiff (-1) δ' δ) hp hm z i j hij k l hk hl hi

/-- The annulus statement for the actual difference of normalized residuals. -/
theorem normalized_residual_annulus {δ' δ : ℝ} (hδ' : 0 < δ') (hδ : δ' ≤ δ) (hsmall : δ ≤ 1/16)
    (n : ℕ) (z : Space n) (k : ℕ) (hk : k ≤ 3)
    (h : iteratedFDeriv ℝ k (fun w => ZeroChainResidual.residual n (flattenMap n δ' w)-
      ZeroChainResidual.residual n (flattenMap n δ w)) z ≠ 0) :
    ∃ i : Fin (n+1), δ' < |z i| ∧ |z i| < 2*δ := by
  rw [normalized_difference_eq hδ' hδ hsmall n] at h
  obtain ⟨i,hi,_⟩ := nonzero_difference_jet_annulus hδ' hδ n z k hk h
  exact ⟨i,hi⟩

end Bilevel.ZeroChainFlatteningAnnulus
