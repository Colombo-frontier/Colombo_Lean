import Bilevel.ChiFineMultiscale
import Bilevel.ChiFineBounds

/-! Amplitude and derivative budgets for the actual revised fine telescope.
The estimates use the centered frontier and incoming-only flattening. -/
noncomputable section
namespace Bilevel.ChiFine.PieceBounds
open ChiBoundedChain ZeroChainResidualBounds

theorem normalized_bounds : ∃ B : ℝ, 1 ≤ B ∧ ∀ n : ℕ,
    (∀ k : Fin 4, ∀ z : Space n, ‖iteratedFDeriv ℝ k.val (centeredResidual n) z‖ ≤ B) ∧
    (∀ δ : ℝ, 0 < δ → δ ≤ 1/16 → ∀ z : Space n,
      |flattened n δ z| ≤ B ∧ |centeredResidual n z-flattened n δ z| ≤ B*δ ∧
      ∀ k : Fin 3, ‖iteratedFDeriv ℝ (k.val+1) (flattened n δ) z‖ ≤ B/δ^k.val) := by
  obtain ⟨M,hM,hm⟩ := centered_uniform_jet_bound
  obtain ⟨C,hC,hflat⟩ := flattened_positive_jet_bounds
  let E := 2*Real.sqrt (Real.exp 1)
  let B := M+C+E
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hB : 1 ≤ B := by dsimp [B]; linarith
  have hMB : M ≤ B := by dsimp [B]; linarith
  have hCB : C ≤ B := by dsimp [B]; linarith
  have hEB : E ≤ B := by dsimp [B]; linarith
  refine ⟨B,hB,fun n => ⟨fun k z => (hm n k.val (by omega) z).trans hMB,?_⟩⟩
  intro δ hδ hs z
  refine ⟨?_,?_,fun k => (hflat n δ hδ hs k z).trans
    (div_le_div_of_nonneg_right hCB (by positivity))⟩
  · rw [flattened_eq_latent_composition hδ hs]
    have hh := hm n 0 (by norm_num) (ZeroChainFlatteningMap.flattenMap n δ z)
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hh.trans hMB
  · exact (flattening_error hδ n z).trans (mul_le_mul_of_nonneg_right hEB hδ.le)

theorem coarse_amplitude_bound (B : ℝ) (_hB : 0 ≤ B) (n J : ℕ) (δ : ℕ → ℝ)
    (hbase : ∀ z : Space n,|centeredResidual n z| ≤ B)
    (hflat : ∀ j,j < J → ∀ z : Space n,|flattened n (δ j) z| ≤ B) (z : Space n) :
    |piece n J δ 0 z| ≤ B := by
  by_cases hJ : 0 < J
  · simpa only [piece,approximation,if_pos hJ,flattened] using hflat 0 hJ z
  · simpa only [piece,approximation,if_neg hJ] using hbase z

theorem noncoarse_amplitude_bound (B : ℝ) (hB : 0 ≤ B) (n J : ℕ) (δ : ℕ → ℝ)
    (hpos : ∀ j,j < J → 0 < δ j)
    (hmono : ∀ i j,i ≤ j → j < J → δ j ≤ δ i)
    (herr : ∀ j,j < J → ∀ z : Space n,|centeredResidual n z-flattened n (δ j) z| ≤ B*δ j)
    (i : ℕ) (hi : 1 ≤ i) (hiJ : i ≤ J) (z : Space n) :
    |piece n J δ i z| ≤ 2*B*δ (i-1) := by
  obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  have hl : l < J := by omega
  simp only [piece,approximation,Nat.add_sub_cancel,Nat.succ_sub_one,if_pos hl]
  by_cases hnext : l+1 < J
  · rw [if_pos hnext]
    have h1 := herr (l+1) hnext z
    have h2 := herr l hl z
    have hm := mul_le_mul_of_nonneg_left (hmono l (l+1) (by omega) hnext) hB
    have ht := abs_sub (centeredResidual n z-flattened n (δ l) z) (centeredResidual n z-flattened n (δ (l+1)) z)
    have he : centeredResidual n z-flattened n (δ l) z-(centeredResidual n z-flattened n (δ (l+1)) z) =
        flattened n (δ (l+1)) z-flattened n (δ l) z := by ring
    rw [he] at ht
    change |flattened n (δ (l+1)) z-flattened n (δ l) z| ≤ _
    linarith
  · rw [if_neg hnext]
    change |centeredResidual n z-flattened n (δ l) z| ≤ _
    have h := herr l hl z
    have hp := mul_nonneg hB (hpos l hl).le
    linarith

theorem approximation_positive_bound (B d : ℝ) (hB : 0 ≤ B) (hd : 0 < d) (hd1 : d ≤ 1)
    (n J : ℕ) (δ : ℕ → ℝ)
    (hbase : ∀ k : Fin 3,∀ z : Space n,‖iteratedFDeriv ℝ (k.val+1) (centeredResidual n) z‖ ≤ B)
    (hflat : ∀ t,t < J → ∀ k : Fin 3,∀ z : Space n,
      ‖iteratedFDeriv ℝ (k.val+1) (flattened n (δ t)) z‖ ≤ B/δ t^k.val)
    (t : ℕ) (hdt : t < J → d ≤ δ t) (z : Space n) (k : Fin 3) :
    ‖iteratedFDeriv ℝ (k.val+1) (approximation n J δ t) z‖ ≤ B/d^k.val := by
  by_cases ht : t < J
  · have he : approximation n J δ t = flattened n (δ t) := by ext w; simp [approximation,ht,flattened]
    rw [he]
    exact (hflat t ht k z).trans (div_le_div_of_nonneg_left hB (pow_pos hd _)
      (pow_le_pow_left₀ hd.le (hdt ht) _))
  · have he : approximation n J δ t = centeredResidual n := by ext w; simp [approximation,ht]
    rw [he]
    apply (hbase k z).trans
    apply (le_div_iff₀ (pow_pos hd _)).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (pow_le_one₀ hd.le hd1) hB

theorem piece_positive_bound (B d : ℝ) (hB : 0 ≤ B) (hd : 0 < d) (hd1 : d ≤ 1)
    (n J : ℕ) (δ : ℕ → ℝ)
    (hbase : ∀ k : Fin 3,∀ z : Space n,‖iteratedFDeriv ℝ (k.val+1) (centeredResidual n) z‖ ≤ B)
    (hflat : ∀ t,t < J → ∀ k : Fin 3,∀ z : Space n,
      ‖iteratedFDeriv ℝ (k.val+1) (flattened n (δ t)) z‖ ≤ B/δ t^k.val)
    (i : ℕ) (hcurrent : i < J → d ≤ δ i)
    (hprevious : 1 ≤ i → i-1 < J → d ≤ δ (i-1)) (z : Space n) (k : Fin 3) :
    ‖iteratedFDeriv ℝ (k.val+1) (piece n J δ i) z‖ ≤ 2*B/d^k.val := by
  cases i with
  | zero =>
    have hh := approximation_positive_bound B d hB hd hd1 n J δ hbase hflat 0 hcurrent z k
    change ‖iteratedFDeriv ℝ (k.val+1) (approximation n J δ 0) z‖ ≤ _
    exact hh.trans (div_le_div_of_nonneg_right (by linarith) (pow_nonneg hd.le _))
  | succ l =>
    have h1 := approximation_positive_bound B d hB hd hd1 n J δ hbase hflat (l+1) hcurrent z k
    have h2 := approximation_positive_bound B d hB hd hd1 n J δ hbase hflat l
      (by intro hl; simpa using hprevious (by omega) (by simpa)) z k
    have hh := jet_sub_norm_le (approximation_contDiff n J δ (l+1)) (approximation_contDiff n J δ l)
      z (k.val+1) (by omega)
    change ‖iteratedFDeriv ℝ (k.val+1) (fun w => approximation n J δ (l+1) w-approximation n J δ l w) z‖ ≤ _
    calc
      _ ≤ _ := hh
      _ ≤ B/d^k.val+B/d^k.val := add_le_add h1 h2
      _ = _ := by ring

end Bilevel.ChiFine.PieceBounds
