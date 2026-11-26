import Bilevel.ChiCarrierProductLedger

/-! Separate amplitude and positive-derivative scales for fine pieces.
The zeroth-order amplitude is preserved; first derivatives do not lose 1/delta. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiCarrier

def fineScale (a M δ : ℝ) : ℕ → ℝ
  | 0 => a
  | k+1 => M/δ^k

theorem fineScale_nonneg {a M δ : ℝ} (ha : 0≤a) (hM : 0≤M) (hδ : 0≤δ) (k : ℕ) :
    0≤fineScale a M δ k := by cases k <;> simp only [fineScale] <;> positivity

theorem fineScale_step {a M δ d : ℝ} (hM : 0≤M) (hδ : 0<δ) (hd : 0<d)
    (hδd : δ≤d) (haM : a≤M*d) (s : ℕ) :
    fineScale a M δ s/d≤fineScale a M δ (s+1) := by
  cases s with
  | zero => simpa only [fineScale,pow_zero,div_one] using (div_le_iff₀ hd).mpr haM
  | succ s =>
    simp only [fineScale,pow_succ,div_div]
    exact div_le_div_of_nonneg_left hM (mul_pos (pow_pos hδ s) hδ)
      (mul_le_mul_of_nonneg_left hδd (pow_nonneg hδ.le s))

theorem fineScale_div_pow {a M δ d : ℝ} (hM : 0≤M) (hδ : 0<δ) (hd : 0<d)
    (hδd : δ≤d) (haM : a≤M*d) (s q : ℕ) :
    fineScale a M δ s/d^q≤fineScale a M δ (s+q) := by
  induction q with
  | zero => simp
  | succ q ih =>
    calc
      _ = (fineScale a M δ s/d^q)/d := by rw [pow_succ];ring
      _ ≤ fineScale a M δ (s+q)/d := div_le_div_of_nonneg_right ih hd.le
      _ ≤ _ := fineScale_step hM hδ hd hδd haM (s+q)

theorem coarser_fine_product {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f g : X → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    (Cs Cg a M δ d : ℝ) (hCs : 0≤Cs) (hCg : 0≤Cg) (ha : 0≤a) (hM : 0≤M)
    (hδ : 0<δ) (hd : 0<d) (hδd : δ≤d) (haM : a≤M*d) (x : X) (k : ℕ) (hk : k≤3)
    (hsel : ∀ q,q≤k → ‖iteratedFDeriv ℝ q f x‖≤Cs/d^q)
    (hcore : ∀ q,q≤k → ‖iteratedFDeriv ℝ q g x‖≤Cg*fineScale a M δ q) :
    ‖iteratedFDeriv ℝ k (fun y => f y*g y) x‖≤8*Cs*Cg*fineScale a M δ k := by
  have hs := Bilevel.ZeroChainResidualBounds.jet_mul_bound hf hg x k hk
    (fun q => Cs/d^q) (fun q => Cg*fineScale a M δ q) (fun _ => by positivity) hsel hcore
  have hsum : (∑ q ∈ Finset.range (k+1),(k.choose q:ℝ))≤8 := by
    interval_cases k <;> norm_num [Finset.sum_range_succ]
  have hSk := fineScale_nonneg ha hM hδ.le k
  calc
    _ ≤ ∑ q ∈ Finset.range (k+1),(k.choose q:ℝ)*(Cs/d^q)*(Cg*fineScale a M δ (k-q)) := hs
    _ ≤ ∑ q ∈ Finset.range (k+1),(k.choose q:ℝ)*(Cs*Cg*fineScale a M δ k) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqk : q≤k := by have := Finset.mem_range.mp hq;omega
      have hscale := fineScale_div_pow hM hδ hd hδd haM (k-q) q
      rw [Nat.sub_add_cancel hqk] at hscale
      have hh := mul_le_mul_of_nonneg_left hscale (show 0≤(k.choose q:ℝ)*(Cs*Cg) by positivity)
      convert hh using 1 <;> ring
    _ = (∑ q ∈ Finset.range (k+1),(k.choose q:ℝ))*(Cs*Cg*fineScale a M δ k) :=
      (Finset.sum_mul ..).symm
    _ ≤ 8*(Cs*Cg*fineScale a M δ k) := mul_le_mul_of_nonneg_right hsum (by positivity)
    _ = _ := by ring

end Bilevel.ChiCarrier
