import HeavyTail.ProximalOracle

/-! The manuscript's halving search terminates within the ceiling-logarithmic
number of public proximal evaluations and returns a bounded correction. -/
noncomputable section
open Set
open scoped InnerProductSpace
namespace HeavyTail
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def proximalScale (G R : ℝ) (k : ℕ) : ℝ := (2 * R / G) / (2 : ℝ) ^ k

def proximalCorrection {S : Set E} {h : E → ℝ} (P : ProximalOracle S h)
    (η : ℝ) (z : E) : E := η⁻¹ • (z - P.point η z)

theorem proximalScale_pos {G R : ℝ} (hG : 0 < G) (hR : 0 < R) (k : ℕ) :
    0 < proximalScale G R k := by unfold proximalScale; positivity

theorem proximalScale_succ (G R : ℝ) (k : ℕ) :
    proximalScale G R (k + 1) = proximalScale G R k / 2 := by
  unfold proximalScale
  rw [pow_succ]
  ring

theorem proximalCorrection_norm {S : Set E} {h : E → ℝ} (P : ProximalOracle S h)
    {η : ℝ} (hη : 0 < η) (z : E) :
    ‖proximalCorrection P η z‖ = ‖P.point η z - z‖ / η := by
  rw [proximalCorrection, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hη), norm_sub_rev]
  ring

theorem proximalCorrection_halving {S : Set E} {h : E → ℝ}
    (P : ProximalOracle S h) {η : ℝ} (hη : 0 < η) (z : E) :
    ‖proximalCorrection P (η / 2) z‖ ≤ 2 * ‖proximalCorrection P η z‖ := by
  rw [proximalCorrection_norm P (by positivity), proximalCorrection_norm P hη]
  calc
    _ ≤ ‖P.point η z - z‖ / (η / 2) :=
      div_le_div_of_nonneg_right (proximalOracle_displacement_mono P (by positivity) (by linarith) z)
        (by positivity)
    _ = _ := by ring

theorem proximalScale_deadline {G R : ℝ} {n : ℕ}
    (hG : 0 < G) (hR : 0 < R) (hn : 0 < n) :
    proximalScale G R (Nat.clog 2 (2 * n)) ≤ R / (G * n) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hnPow : (2 : ℝ) * n ≤ (2 : ℝ) ^ Nat.clog 2 (2 * n) := by
    exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) (2 * n)
  unfold proximalScale
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ Nat.clog 2 (2 * n))).mpr
  have h := mul_le_mul_of_nonneg_left hnPow (show 0 ≤ R / (G * n) by positivity)
  have he : R / (G * n) * ((2 : ℝ) * n) = 2 * R / G := by field_simp; ring
  rw [he] at h
  exact h

theorem proximalCorrection_initial_bound {S : Set E} {h : E → ℝ} {G R : ℝ}
    (P : ProximalOracle S h) (hG : 0 < G) (hR : 0 < R)
    (z xstar : E) (hx : xstar ∈ S) (hz : ‖z - xstar‖ ≤ 2 * R)
    (hlower : ∀ u ∈ S, h xstar - G * ‖u - xstar‖ ≤ h u) :
    ‖proximalCorrection P (proximalScale G R 0) z‖ ≤ 3 * G := by
  have hη := proximalScale_pos hG hR 0
  rw [proximalCorrection_norm P hη]
  apply (div_le_iff₀ hη).mpr
  have hd := proximalOracle_displacement_bound P hη hG.le z xstar hx hlower
  have he : 2 * proximalScale G R 0 * G + 2 * R = 3 * G * proximalScale G R 0 := by
    simp only [proximalScale, pow_zero, div_one]
    field_simp
    ring
  linarith only [hd, hz, he]

/-- The selected proximal point and correction obey all three clauses of
`eq:correction`. Its index bounds the number of proximal calls by clog₂(2n)+1. -/
theorem proximal_halving_search {S : Set E} {h : E → ℝ} {G R : ℝ} {n : ℕ}
    (P : ProximalOracle S h) (hh : ConvexOn ℝ S h)
    (hG : 0 < G) (hR : 0 < R) (hn : 0 < n)
    (z xstar : E) (hx : xstar ∈ S) (hz : ‖z - xstar‖ ≤ 2 * R)
    (hlower : ∀ u ∈ S, h xstar - G * ‖u - xstar‖ ≤ h u) :
    ∃ k ≤ Nat.clog 2 (2 * n),
      let η := proximalScale G R k
      let y := P.point η z
      let a := proximalCorrection P η z
      0 < η ∧ y ∈ S ∧ ‖a‖ ≤ 3 * G ∧
      (G ≤ ‖a‖ ∨ η ≤ R / (G * n)) ∧
      z - y = η • a ∧ (∀ u ∈ S, h y - h u ≤ ⟪a, y - u⟫_ℝ) := by
  classical
  let stop := fun k => G ≤ ‖proximalCorrection P (proximalScale G R k) z‖ ∨
    proximalScale G R k ≤ R / (G * n)
  have hex : ∃ k, k ≤ Nat.clog 2 (2 * n) ∧ stop k :=
    ⟨Nat.clog 2 (2 * n), le_rfl, Or.inr (proximalScale_deadline hG hR hn)⟩
  let k := Nat.find hex
  have hk : k ≤ Nat.clog 2 (2 * n) ∧ stop k := Nat.find_spec hex
  have hbound : ‖proximalCorrection P (proximalScale G R k) z‖ ≤ 3 * G := by
    cases hkind : k with
    | zero =>
        exact proximalCorrection_initial_bound P hG hR z xstar hx hz hlower
    | succ j =>
        have hj : j < k := by omega
        have hmin : ¬(j ≤ Nat.clog 2 (2 * n) ∧ stop j) := Nat.find_min hex hj
        have hnot : ¬stop j := fun hstop => hmin ⟨by omega, hstop⟩
        have hsmall : ‖proximalCorrection P (proximalScale G R j) z‖ < G :=
          lt_of_not_ge (fun hg => hnot (Or.inl hg))
        rw [proximalScale_succ]
        have hd := proximalCorrection_halving P (proximalScale_pos hG hR j) z
        linarith only [hd, hsmall, hG]
  refine ⟨k, hk.1, proximalScale_pos hG hR k,
    P.feasible _ (proximalScale_pos hG hR k) z, hbound, hk.2, ?_, ?_⟩
  · simp only [proximalCorrection, smul_smul, mul_inv_cancel₀ (proximalScale_pos hG hR k).ne',
      one_smul]
  · exact fun u hu => proximalOracle_subgradient P hh (proximalScale_pos hG hR k) z u hu

end HeavyTail
