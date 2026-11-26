import Mathlib

/-!
# Finite power-mean inequality for the boost analysis

This is the normalized finite Jensen step used to pass from a dyadic
square-energy estimate to the `a`-power estimate for `0 ≤ a ≤ 2`.
-/

open Finset Set

namespace VIReference.Pilot

/-- Normalized finite power mean in precisely the form needed on each dyadic
block of warm-start distances. -/
theorem finite_power_mean_normalized
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (hs : s.Nonempty)
    (r : ι → ℝ) (hr : ∀ i ∈ s, 0 ≤ r i)
    (a : ℝ) (ha0 : 0 ≤ a) (ha2 : a ≤ 2) :
    (1 / (s.card : ℝ)) * ∑ i ∈ s, Real.rpow (r i) a ≤
      Real.rpow ((1 / (s.card : ℝ)) * ∑ i ∈ s, (r i) ^ 2) (a / 2) := by
  let q : ℝ := a / 2
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hq1 : q ≤ 1 := by dsimp [q]; linarith
  have hcard : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
  have hw : ∑ _i ∈ s, (1 / (s.card : ℝ)) = 1 := by
    simp [hcard]
  have hj := (Real.concaveOn_rpow hq0 hq1).le_map_sum
    (t := s) (w := fun _i => (1 / (s.card : ℝ)))
    (p := fun i => (r i) ^ 2)
    (fun _ _ => by positivity) hw
    (fun i hi => by exact sq_nonneg (r i))
  simp only [smul_eq_mul] at hj
  have hdiag : ∀ i ∈ s,
      Real.rpow ((r i) ^ 2) q = Real.rpow (r i) a := by
    intro i hi
    calc
      Real.rpow ((r i) ^ 2) q =
          Real.rpow (Real.rpow (r i) (2 : ℝ)) q := by
            congr 1
            exact (Real.rpow_natCast (r i) 2).symm
      _ = Real.rpow (r i) ((2 : ℝ) * q) :=
        (Real.rpow_mul (hr i hi) 2 q).symm
      _ = Real.rpow (r i) a := by
        congr 1
        dsimp [q]
        ring
  calc
    (1 / (s.card : ℝ)) * ∑ i ∈ s, Real.rpow (r i) a =
        ∑ i ∈ s, (1 / (s.card : ℝ)) * Real.rpow (r i) a := by
          rw [Finset.mul_sum]
    _ = ∑ i ∈ s, (1 / (s.card : ℝ)) *
        Real.rpow ((r i) ^ 2) q := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hdiag i hi]
    _ ≤ Real.rpow
        (∑ i ∈ s, (1 / (s.card : ℝ)) * (r i) ^ 2) q := hj
    _ = Real.rpow ((1 / (s.card : ℝ)) * ∑ i ∈ s, (r i) ^ 2)
        (a / 2) := by rw [Finset.mul_sum]

/-- Unnormalized form used verbatim in the source's dyadic block estimate. -/
theorem finite_power_mean
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (hs : s.Nonempty)
    (r : ι → ℝ) (hr : ∀ i ∈ s, 0 ≤ r i)
    (a : ℝ) (ha0 : 0 ≤ a) (ha2 : a ≤ 2) :
    ∑ i ∈ s, Real.rpow (r i) a ≤
      Real.rpow (s.card : ℝ) (1 - a / 2) *
        Real.rpow (∑ i ∈ s, (r i) ^ 2) (a / 2) := by
  let c : ℝ := s.card
  let q : ℝ := a / 2
  have hc : 0 < c := by
    dsimp [c]
    exact_mod_cast hs.card_pos
  have hsum : 0 ≤ ∑ i ∈ s, (r i) ^ 2 := by positivity
  have hnorm := finite_power_mean_normalized s hs r hr a ha0 ha2
  have hmul := mul_le_mul_of_nonneg_left hnorm hc.le
  have hfactor :
      c * Real.rpow ((1 / c) * ∑ i ∈ s, (r i) ^ 2) q =
        Real.rpow c (1 - q) *
          Real.rpow (∑ i ∈ s, (r i) ^ 2) q := by
    have hmr : Real.rpow (c⁻¹ * ∑ i ∈ s, (r i) ^ 2) q =
        Real.rpow c⁻¹ q * Real.rpow (∑ i ∈ s, (r i) ^ 2) q :=
      Real.mul_rpow (show 0 ≤ c⁻¹ by positivity) hsum
    have hinv : Real.rpow c⁻¹ q = (Real.rpow c q)⁻¹ :=
      Real.inv_rpow hc.le q
    have hsub : Real.rpow c (1 - q) =
        Real.rpow c 1 / Real.rpow c q := Real.rpow_sub hc 1 q
    have hone : Real.rpow c 1 = c := Real.rpow_one c
    rw [one_div, hmr, hinv]
    rw [hsub, hone]
    field_simp [(Real.rpow_pos_of_pos hc q).ne']
  change c * ((1 / c) * ∑ i ∈ s, Real.rpow (r i) a) ≤
    c * Real.rpow ((1 / c) * ∑ i ∈ s, (r i) ^ 2) q at hmul
  have hleft : c * ((1 / c) * ∑ i ∈ s, Real.rpow (r i) a) =
      ∑ i ∈ s, Real.rpow (r i) a := by
    field_simp
  rw [hleft, hfactor] at hmul
  simpa [c, q] using hmul

/-- Direct dyadic-block corollary: any square-energy majorant can be raised
to an `a/2` power without introducing a pointwise claim. -/
theorem dyadic_power_sum_of_energy
    (r : ℕ → ℝ) {k ell : ℕ} (hkle : k ≤ ell)
    (hr : ∀ t ∈ Finset.Icc k ell, 0 ≤ r t)
    (a B : ℝ) (ha0 : 0 ≤ a) (ha2 : a ≤ 2) (hB0 : 0 ≤ B)
    (henergy : ∑ t ∈ Finset.Icc k ell, (r t) ^ 2 ≤ B) :
    ∑ t ∈ Finset.Icc k ell, Real.rpow (r t) a ≤
      Real.rpow ((Finset.Icc k ell).card : ℝ) (1 - a / 2) *
        Real.rpow B (a / 2) := by
  have hmean := finite_power_mean (Finset.Icc k ell)
    (Finset.nonempty_Icc.mpr hkle) r hr a ha0 ha2
  have hsum0 : 0 ≤ ∑ t ∈ Finset.Icc k ell, (r t) ^ 2 := by positivity
  have hrpow := Real.rpow_le_rpow hsum0 henergy (by linarith : 0 ≤ a / 2)
  exact hmean.trans (mul_le_mul_of_nonneg_left hrpow
    (Real.rpow_nonneg (by positivity) _))

/-- Exact scalar normalization behind the source's dyadic warm-start bound.
It records, without hiding any constant, that raising the block energy
`256 * R² * h² / x²` to `a/2` produces `16^a` and the exponent
`1 - 3a/2` after multiplication by the block-cardinality factor. -/
theorem dyadic_warm_power_normalization
    (a R h x : ℝ) (hR : 0 ≤ R) (hh : 0 ≤ h) (hx : 0 < x) :
    Real.rpow x (1 - a / 2) *
        Real.rpow (256 * (R ^ 2 * h ^ 2) / x ^ 2) (a / 2) =
      Real.rpow 16 a * Real.rpow R a * Real.rpow h a *
        Real.rpow x (1 - 3 * a / 2) := by
  let q : ℝ := a / 2
  have ha : a = 2 * q := by dsimp [q]; ring
  have h256 : Real.rpow (256 : ℝ) q = Real.rpow 16 a := by
    calc
      Real.rpow (256 : ℝ) q = Real.rpow ((16 : ℝ) ^ 2) q := by norm_num
      _ = Real.rpow (Real.rpow 16 (2 : ℝ)) q := by
        congr 1
        exact (Real.rpow_natCast 16 2).symm
      _ = Real.rpow 16 ((2 : ℝ) * q) :=
        (Real.rpow_mul (by positivity : (0 : ℝ) ≤ 16) 2 q).symm
      _ = Real.rpow 16 a := by rw [ha]
  have hR2 : Real.rpow (R ^ 2) q = Real.rpow R a := by
    calc
      Real.rpow (R ^ 2) q = Real.rpow (Real.rpow R (2 : ℝ)) q := by
        congr 1
        exact (Real.rpow_natCast R 2).symm
      _ = Real.rpow R ((2 : ℝ) * q) := (Real.rpow_mul hR 2 q).symm
      _ = Real.rpow R a := by rw [ha]
  have hh2 : Real.rpow (h ^ 2) q = Real.rpow h a := by
    calc
      Real.rpow (h ^ 2) q = Real.rpow (Real.rpow h (2 : ℝ)) q := by
        congr 1
        exact (Real.rpow_natCast h 2).symm
      _ = Real.rpow h ((2 : ℝ) * q) := (Real.rpow_mul hh 2 q).symm
      _ = Real.rpow h a := by rw [ha]
  have hx2 : Real.rpow (x ^ 2) q = Real.rpow x (2 * q) := by
    calc
      Real.rpow (x ^ 2) q = Real.rpow (Real.rpow x (2 : ℝ)) q := by
        congr 1
        exact (Real.rpow_natCast x 2).symm
      _ = Real.rpow x ((2 : ℝ) * q) := (Real.rpow_mul hx.le 2 q).symm
  have hinside :
      Real.rpow (256 * (R ^ 2 * h ^ 2) / x ^ 2) q =
        Real.rpow 16 a * Real.rpow R a * Real.rpow h a /
          Real.rpow x (2 * q) := by
    calc
      Real.rpow (256 * (R ^ 2 * h ^ 2) / x ^ 2) q =
          Real.rpow (256 * (R ^ 2 * h ^ 2)) q /
            Real.rpow (x ^ 2) q :=
        Real.div_rpow (by positivity) (sq_nonneg x) q
      _ = (Real.rpow 256 q * Real.rpow (R ^ 2 * h ^ 2) q) /
            Real.rpow (x ^ 2) q := by
        change ((256 * (R ^ 2 * h ^ 2)) ^ q : ℝ) / (x ^ 2) ^ q =
          (256 : ℝ) ^ q * (R ^ 2 * h ^ 2) ^ q / (x ^ 2) ^ q
        rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 256) (by positivity)]
      _ = (Real.rpow 256 q *
            (Real.rpow (R ^ 2) q * Real.rpow (h ^ 2) q)) /
            Real.rpow (x ^ 2) q := by
        change (256 : ℝ) ^ q * (R ^ 2 * h ^ 2) ^ q / (x ^ 2) ^ q =
          (256 : ℝ) ^ q * ((R ^ 2) ^ q * (h ^ 2) ^ q) / (x ^ 2) ^ q
        rw [Real.mul_rpow (sq_nonneg R) (sq_nonneg h)]
      _ = _ := by rw [h256, hR2, hh2, hx2]; ring
  rw [show a / 2 = q by rfl, hinside]
  rw [show 1 - 3 * a / 2 = (1 - q) - 2 * q by dsimp [q]; ring]
  have hxcombine :
      Real.rpow x (1 - q) / Real.rpow x (2 * q) =
        Real.rpow x ((1 - q) - 2 * q) :=
    (Real.rpow_sub hx (1 - q) (2 * q)).symm
  calc
    Real.rpow x (1 - q) *
        (Real.rpow 16 a * Real.rpow R a * Real.rpow h a /
          Real.rpow x (2 * q)) =
      (Real.rpow 16 a * Real.rpow R a * Real.rpow h a) *
        (Real.rpow x (1 - q) / Real.rpow x (2 * q)) := by ring
    _ = _ := by rw [hxcombine]

/-- Sum over a finite union is at most the iterated sum when all summands are
nonnegative.  This form intentionally does not require proving the blocks
disjoint. -/
theorem sum_biUnion_le_iterated
    {α ι : Type*} [DecidableEq ι] (s : Finset α) (t : α → Finset ι)
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∑ i ∈ s.biUnion t, f i ≤ ∑ j ∈ s, ∑ i ∈ t j, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hjs ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert hjs]
      have hinter : 0 ≤ ∑ i ∈ t j ∩ s.biUnion t, f i := by
        exact Finset.sum_nonneg fun i _ ↦ hf i
      have hunion := Finset.sum_union_inter (s₁ := t j)
        (s₂ := s.biUnion t) (f := f)
      calc
        ∑ i ∈ t j ∪ s.biUnion t, f i ≤
            (∑ i ∈ t j, f i) + (∑ i ∈ s.biUnion t, f i) := by
              linarith
        _ ≤ (∑ i ∈ t j, f i) +
            (∑ x ∈ s, ∑ i ∈ t x, f i) := by gcongr

/-- The public dyadic blocks cover exactly the indices `2,…,K`. -/
theorem dyadic_blocks_cover (K : ℕ) (hK : 2 ≤ K) :
    (Finset.Icc 1 (Nat.log 2 K)).biUnion
        (fun j => Finset.Icc (2 ^ j) (min (2 ^ (j + 1) - 1) K)) =
      Finset.Icc 2 K := by
  classical
  ext n
  constructor
  · intro hn
    obtain ⟨j, hj, hnblock⟩ := Finset.mem_biUnion.mp hn
    have hj' := Finset.mem_Icc.mp hj
    have hn' := Finset.mem_Icc.mp hnblock
    apply Finset.mem_Icc.mpr
    constructor
    · exact (show 2 ^ 1 ≤ 2 ^ j from Nat.pow_le_pow_right (by omega) hj'.1) |>.trans hn'.1
    · exact hn'.2.trans (min_le_right _ _)
  · intro hn
    have hn' := Finset.mem_Icc.mp hn
    let j := Nat.log 2 n
    have hn0 : n ≠ 0 := by omega
    have hj1 : 1 ≤ j := by
      exact Nat.le_log_of_pow_le (by omega) (by simpa using hn'.1)
    have hjK : j ≤ Nat.log 2 K := Nat.log_mono_right hn'.2
    apply Finset.mem_biUnion.mpr
    refine ⟨j, Finset.mem_Icc.mpr ⟨hj1, hjK⟩, ?_⟩
    apply Finset.mem_Icc.mpr
    constructor
    · exact Nat.pow_log_le_self 2 hn0
    · apply le_min
      · have hlt := Nat.lt_pow_succ_log_self (by omega : 1 < 2) n
        dsimp [j]
        omega
      · exact hn'.2

/-- Consequently a nonnegative sum on `2,…,K` is bounded by the sum over
all public dyadic blocks used in `U_a(K)`. -/
theorem sum_Icc_two_le_dyadic_blocks
    (K : ℕ) (hK : 2 ≤ K) (f : ℕ → ℝ) (hf : ∀ t, 0 ≤ f t) :
    ∑ t ∈ Finset.Icc 2 K, f t ≤
      ∑ j ∈ Finset.Icc 1 (Nat.log 2 K),
        ∑ t ∈ Finset.Icc (2 ^ j) (min (2 ^ (j + 1) - 1) K), f t := by
  rw [← dyadic_blocks_cover K hK]
  exact sum_biUnion_le_iterated _ _ f hf

end VIReference.Pilot
