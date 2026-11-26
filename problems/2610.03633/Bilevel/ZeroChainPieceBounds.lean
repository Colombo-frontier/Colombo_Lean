import Bilevel.ZeroChainMultiscale
import Bilevel.ZeroChainFlatteningBounds

/-! Actual amplitude and positive-jet budgets of the finite multiscale
pieces, before radial/frame composition. The fine amplitudes use flattening
error rather than the coarse residual amplitude. -/

noncomputable section
namespace Bilevel.ZeroChainPieceBounds
open ZeroChain ZeroChainMultiscale ZeroChainResidual ZeroChainResidualBounds
open ZeroChainFlatteningMap ZeroChainFlatteningBounds ZeroChainFlatteningError

def Flat (n : ℕ) (δ : ℝ) (z : Space n) : ℝ := residual n (flattenMap n δ z)

theorem flat_eq (n : ℕ) (δ : ℝ) : Flat n δ = flattenedResidual n 1 1 δ := by
  ext z
  simp only [Flat,flattenedResidual,ZeroChainResidualScaled.R,ZeroChainResidualScaled.scaled,
    inv_one,one_smul,one_mul]

theorem flat_contDiff (n : ℕ) (δ : ℝ) : ContDiff ℝ 3 (Flat n δ) :=
  (residual_contDiff n).comp (flattenMap_contDiff n δ)

theorem normalized_bounds : ∃ B : ℝ, 1 ≤ B ∧ ∀ n : ℕ,
    (∀ k : Fin 4,∀ z : Space n,‖iteratedFDeriv ℝ k.val (residual n) z‖ ≤ B) ∧
    (∀ δ : ℝ,0 < δ → δ ≤ 1/16 → ∀ z : Space n,
      |Flat n δ z| ≤ B ∧ |residual n z-Flat n δ z| ≤ B*δ ∧
      ∀ k : Fin 3,‖iteratedFDeriv ℝ (k.val+1) (Flat n δ) z‖ ≤ B/δ^k.val) := by
  obtain ⟨b,hb0,hb⟩ := residual_uniform_jet_bound
  obtain ⟨C,hC,hflat⟩ := amplitude_derivative_bounds
  let B := 1+(∑ k,b k)+C+errorConstant
  have hC0 : 0 ≤ C := by linarith
  have he0 := errorConstant_pos.le
  have hs : 0 ≤ ∑ k,b k := Finset.sum_nonneg (fun k _ => hb0 k)
  have hB : 1 ≤ B := by dsimp [B]; linarith
  have hCB : C ≤ B := by dsimp [B]; linarith
  have heB : errorConstant ≤ B := by dsimp [B]; linarith
  have hbB (k : Fin 4) : b k ≤ B := by
    have hh := Finset.single_le_sum (fun l (_ : l ∈ Finset.univ) => hb0 l) (Finset.mem_univ k)
    dsimp [B]
    linarith
  refine ⟨B,hB,fun n => ⟨fun k z => (hb k n z).trans (hbB k),?_⟩⟩
  intro δ hδ hδs z
  have hh := hflat n 1 1 δ (by norm_num) (by norm_num) hδ (by linarith) z
  rw [← flat_eq] at hh
  simp only [mul_one,one_mul] at hh
  refine ⟨hh.1.trans hCB,?_,fun k => (hh.2 k).trans (div_le_div_of_nonneg_right hCB (by positivity))⟩
  have he := normalized_error hδ hδs n z
  exact he.trans (mul_le_mul_of_nonneg_right heB hδ.le)

theorem coarse_amplitude_bound (B : ℝ) (_hB : 0 ≤ B) (n J : ℕ) (δ : ℕ → ℝ)
    (hbase : ∀ z : Space n,|residual n z| ≤ B)
    (hflat : ∀ j,j < J → ∀ z : Space n,|Flat n (δ j) z| ≤ B) (z : Space n) :
    |piece n J δ 0 z| ≤ B := by
  by_cases hJ : 0 < J
  · simpa only [piece,approximation,if_pos hJ,Flat] using hflat 0 hJ z
  · simpa only [piece,approximation,if_neg hJ] using hbase z

theorem noncoarse_amplitude_bound (B : ℝ) (hB : 0 ≤ B) (n J : ℕ) (δ : ℕ → ℝ)
    (hpos : ∀ j,j < J → 0 < δ j)
    (hmono : ∀ i j,i ≤ j → j < J → δ j ≤ δ i)
    (herr : ∀ j,j < J → ∀ z : Space n,|residual n z-Flat n (δ j) z| ≤ B*δ j)
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
    have ht := abs_sub (residual n z-Flat n (δ l) z) (residual n z-Flat n (δ (l+1)) z)
    have he : residual n z-Flat n (δ l) z-(residual n z-Flat n (δ (l+1)) z) =
        Flat n (δ (l+1)) z-Flat n (δ l) z := by ring
    rw [he] at ht
    change |Flat n (δ (l+1)) z-Flat n (δ l) z| ≤ _
    linarith
  · rw [if_neg hnext]
    change |residual n z-Flat n (δ l) z| ≤ _
    have h := herr l hl z
    have hp := mul_nonneg hB (hpos l hl).le
    linarith

theorem approximation_positive_bound (B d : ℝ) (hB : 0 ≤ B) (hd : 0 < d) (hd1 : d ≤ 1)
    (n J : ℕ) (δ : ℕ → ℝ)
    (hbase : ∀ k : Fin 3,∀ z : Space n,‖iteratedFDeriv ℝ (k.val+1) (residual n) z‖ ≤ B)
    (hflat : ∀ t,t < J → ∀ k : Fin 3,∀ z : Space n,
      ‖iteratedFDeriv ℝ (k.val+1) (Flat n (δ t)) z‖ ≤ B/δ t^k.val)
    (t : ℕ) (hdt : t < J → d ≤ δ t) (z : Space n) (k : Fin 3) :
    ‖iteratedFDeriv ℝ (k.val+1) (approximation n J δ t) z‖ ≤ B/d^k.val := by
  by_cases ht : t < J
  · have he : approximation n J δ t = Flat n (δ t) := by ext w; simp [approximation,ht,Flat]
    rw [he]
    exact (hflat t ht k z).trans (div_le_div_of_nonneg_left hB (pow_pos hd _)
      (pow_le_pow_left₀ hd.le (hdt ht) _))
  · have he : approximation n J δ t = residual n := by ext w; simp [approximation,ht]
    rw [he]
    apply (hbase k z).trans
    apply (le_div_iff₀ (pow_pos hd _)).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (pow_le_one₀ hd.le hd1) hB

theorem piece_positive_bound (B d : ℝ) (hB : 0 ≤ B) (hd : 0 < d) (hd1 : d ≤ 1)
    (n J : ℕ) (δ : ℕ → ℝ)
    (hbase : ∀ k : Fin 3,∀ z : Space n,‖iteratedFDeriv ℝ (k.val+1) (residual n) z‖ ≤ B)
    (hflat : ∀ t,t < J → ∀ k : Fin 3,∀ z : Space n,
      ‖iteratedFDeriv ℝ (k.val+1) (Flat n (δ t)) z‖ ≤ B/δ t^k.val)
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

end Bilevel.ZeroChainPieceBounds
