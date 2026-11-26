import SecondOrder.CurvatureRandomizedLowerBound

open scoped Classical

namespace SecondOrder
noncomputable section

def curvatureResponseCap (D R : ℝ) : ℕ := ⌊R^2/(65536*D)⌋₊

theorem curvatureResponseCap_bounds {D R : ℝ} (hD : 0<D) (hsize : 131072*D≤R^2) :
    0<curvatureResponseCap D R ∧
      R^2/(131072*D)≤(curvatureResponseCap D R:ℝ) ∧
      (curvatureResponseCap D R:ℝ)≤R^2/(65536*D) := by
  have hx : 2≤R^2/(65536*D) := (le_div_iff₀ (by positivity)).2 (by nlinarith only [hsize])
  have hfloor := Nat.lt_floor_add_one (R^2/(65536*D))
  refine ⟨Nat.floor_pos.2 (by linarith only [hx]),?_,Nat.floor_le (by positivity)⟩
  have he : R^2/(131072*D)=(R^2/(65536*D))/2 := by ring
  rw [he]
  change (R^2/(65536*D))/2≤(⌊R^2/(65536*D)⌋₊:ℝ)
  linarith only [hx,hfloor]

theorem curvatureResponseCap_information {m : ℕ} (hm : 0<m) {R : ℝ} (hR : 2≤R) :
    curvatureArrayInformation m R*curvatureResponseCap ((2*m:ℕ):ℝ) R≤((2*m:ℕ):ℝ)/65536 := by
  have hD : (0:ℝ)<((2*m:ℕ):ℝ) := by exact_mod_cast Nat.mul_pos (by omega) hm
  have hR0 : R≠0 := by linarith
  have hcap : (curvatureResponseCap ((2*m:ℕ):ℝ) R:ℝ)≤R^2/(65536*((2*m:ℕ):ℝ)) :=
    Nat.floor_le (by positivity)
  have hh := mul_le_mul_of_nonneg_left hcap (curvatureArrayInformation_nonneg m R)
  have he : curvatureArrayInformation m R*(R^2/(65536*((2*m:ℕ):ℝ)))=
      (((2*m:ℕ):ℝ)-1)/131072 := by
    rw [curvatureArrayInformation_eq]
    field_simp [hD.ne',hR0]
    <;> ring
  rw [he] at hh
  linarith only [hh,hD]

/-- The link count is one less than the block count; the extra margin makes
that convention explicit when taking a quantitative floor lower bound. -/
theorem curvatureBudgetLinks_lower {Δ A : ℝ} (hA : 0<A) (hsize : 8*A≤Δ) :
    0<curvatureBudgetLinks Δ A ∧ Δ/(4*A)≤(curvatureBudgetLinks Δ A:ℝ) ∧
      (curvatureBudgetLinks Δ A:ℝ)≤Δ/(2*A) := by
  have hΔ : 0<Δ := by linarith
  have hx : 4≤Δ/(2*A) := (le_div_iff₀ (by positivity)).2 (by linarith only [hsize])
  have hn := curvatureBudgetLinks_count (Δ := Δ) hA (by linarith only [hsize,hA])
  have hnr : (curvatureBudgetLinks Δ A:ℝ)+1=(⌊Δ/(2*A)⌋₊:ℝ) := by exact_mod_cast hn
  have hf := Nat.lt_floor_add_one (Δ/(2*A))
  have hf' := Nat.floor_le (div_nonneg hΔ.le (by positivity : 0≤2*A))
  have he : Δ/(4*A)=(Δ/(2*A))/2 := by ring
  have hl : Δ/(4*A)≤(curvatureBudgetLinks Δ A:ℝ) := by rw [he]; linarith only [hx,hnr,hf]
  refine ⟨?_,hl,?_⟩
  · have hpos : (0:ℝ)<(curvatureBudgetLinks Δ A:ℝ) := lt_of_lt_of_le (by positivity) hl
    exact_mod_cast hpos
  · linarith only [hnr,hf']

theorem curvatureIntegerBudget_lower {Δ A D R : ℝ} (hA : 0<A) (hD : 0<D)
    (hsize : 8*A≤Δ) (hcap : 131072*D≤R^2) :
    Δ*R^2/(1048576*A*D)≤((curvatureBudgetLinks Δ A:ℝ)*(curvatureResponseCap D R:ℝ))/2 := by
  have ht := curvatureBudgetLinks_lower hA hsize
  have hc := curvatureResponseCap_bounds hD hcap
  have hΔ : 0≤Δ := by linarith
  have hh := mul_le_mul ht.2.1 hc.2.1 (by positivity : 0≤R^2/(131072*D)) (Nat.cast_nonneg _)
  apply le_trans _ (div_le_div_of_nonneg_right hh (by norm_num))
  exact le_of_eq (by ring)

end
end SecondOrder
