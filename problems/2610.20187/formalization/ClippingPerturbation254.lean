import RationalSpectralClip254

noncomputable section
open scoped Matrix.Norms.Operator
namespace Paper254

theorem scalarClip_eq_max_min (l u x : ℝ) (hlu : l≤u) :
    scalarClip l u x=max l (min u x) := by
  unfold scalarClip
  by_cases hl : x≤l
  · rw [max_eq_right (by linarith),max_eq_right (by linarith),min_eq_right (hl.trans hlu),max_eq_left hl]
    ring
  · by_cases hu : x≤u
    · rw [max_eq_left (by linarith),max_eq_right (by linarith),min_eq_right hu,max_eq_right (by linarith)]
      ring
    · rw [max_eq_left (by linarith),max_eq_left (by linarith),min_eq_left (by linarith),max_eq_right hlu]
      ring

theorem scalarClip_threshold_error (l u l' u' x h : ℝ) (hlu : l≤u) (hlu' : l'≤u')
    (hh : 0≤h) (hl : |l-l'|≤h) (hu : |u-u'|≤h) :
    |scalarClip l u x-scalarClip l' u' x|≤h := by
  rw [scalarClip_eq_max_min _ _ _ hlu,scalarClip_eq_max_min _ _ _ hlu']
  have hm := abs_min_sub_min_le_max u x u' x
  have hn : |min u x-min u' x|≤h := by
    apply hm.trans
    exact max_le hu (by simpa using hh)
  exact (abs_max_sub_max_le_max l (min u x) l' (min u' x)).trans (max_le hl hn)

theorem spectralClip_threshold_error {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ)
    (c : Coordinates d) (l u l' u' h : ℝ) (hlu : l≤u) (hlu' : l'≤u')
    (hh : 0≤h) (hl : |l-l'|≤h) (hu : |u-u'|≤h) :
    ‖rotatedPrecision U (fun j=>scalarClip l u (c j))-
      rotatedPrecision U (fun j=>scalarClip l' u' (c j))‖≤(d:ℝ)^2*h := by
  rw [rotatedPrecision_sub]
  exact rotatedPrecision_norm_bound U _ h hh
    (fun j=>scalarClip_threshold_error l u l' u' (c j) h hlu hlu' hh hl hu)

theorem rounded_spectralClip_original_error {d : ℕ} (hd : 0<d) (a L s p : ℕ)
    (hdim : (d:ℝ)≤(2:ℝ)^a) (ε l u : ℚ) (he : 0<(ε:ℝ))
    (M : Matrix (Fin d) (Fin d) ℚ) (U : Matrix.unitaryGroup (Fin d) ℝ)
    (c : Coordinates d) (hM : realMatrix M=rotatedPrecision U c)
    (hsmall : ((2:ℝ)^L)⁻¹≤(ε:ℝ))
    (hlc : ∀ j,|c j-(l:ℝ)|+(ε:ℝ)≤(2:ℝ)^L)
    (huc : ∀ j,|c j-(u:ℝ)|+(ε:ℝ)≤(2:ℝ)^L)
    (lo hi h : ℝ) (hlu : (l:ℝ)≤(u:ℝ)) (hlh : lo≤hi) (hh : 0≤h)
    (hl : |(l:ℝ)-lo|≤h) (hu : |(u:ℝ)-hi|≤h) :
    ∀ i j,|(roundRationalMatrix p (rationalSpectralClip a L s ε l u M) i j:ℝ)-
      rotatedPrecision U (fun k=>scalarClip lo hi (c k)) i j|≤
      ((2:ℝ)^p)⁻¹+((2:ℝ)^s)⁻¹+(d:ℝ)^2*(ε:ℝ)+(d:ℝ)^2*h := by
  have hs := spectralClip_threshold_error U c (l:ℝ) (u:ℝ) lo hi h hlu hlh hh hl hu
  intro i j
  have h1 := roundRationalMatrix_entry p (rationalSpectralClip a L s ε l u M) i j
  have h2 := rationalSpectralClip_error hd a L s hdim ε l u he M U c hM hsmall hlc huc i j
  have h3 := (matrix_entry_le_operator_norm
    (rotatedPrecision U (fun k=>scalarClip (l:ℝ) (u:ℝ) (c k))-
      rotatedPrecision U (fun k=>scalarClip lo hi (c k))) i j).trans hs
  change |(rationalSpectralClip a L s ε l u M i j:ℝ)-_|≤_ at h2
  change |rotatedPrecision U (fun k=>scalarClip (l:ℝ) (u:ℝ) (c k)) i j-
    rotatedPrecision U (fun k=>scalarClip lo hi (c k)) i j|≤_ at h3
  obtain ⟨h10,h11⟩ := abs_le.mp h1
  obtain ⟨h20,h21⟩ := abs_le.mp h2
  obtain ⟨h30,h31⟩ := abs_le.mp h3
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end Paper254
#print axioms Paper254.rounded_spectralClip_original_error
