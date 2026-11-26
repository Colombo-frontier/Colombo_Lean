import SecondOrder.LocalSmoothness

namespace SecondOrder
noncomputable section
variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A globally bounded map with a finite global Lipschitz constant. -/
def BoundedLipschitz (f : E → F) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ (∀ x, ‖f x‖ ≤ C) ∧ ∀ x y, ‖f x-f y‖ ≤ C*‖x-y‖

theorem boundedLipschitz_const (c : F) : BoundedLipschitz (fun _ : E => c) := by
  refine ⟨‖c‖, norm_nonneg _, fun _ => le_rfl, ?_⟩
  intro x y
  simp only [sub_self, norm_zero]
  positivity

theorem BoundedLipschitz.add {f g : E → F} (hf : BoundedLipschitz f)
    (hg : BoundedLipschitz g) : BoundedLipschitz (fun x => f x+g x) := by
  obtain ⟨C,hC,hf,hfl⟩ := hf
  obtain ⟨D,hD,hg,hgl⟩ := hg
  refine ⟨C+D, add_nonneg hC hD, fun x => (norm_add_le _ _).trans (add_le_add (hf x) (hg x)), ?_⟩
  intro x y
  calc
    ‖f x+g x-(f y+g y)‖ = ‖(f x-f y)+(g x-g y)‖ := by congr 1; abel
    _ ≤ ‖f x-f y‖+‖g x-g y‖ := norm_add_le _ _
    _ ≤ C*‖x-y‖+D*‖x-y‖ := add_le_add (hfl x y) (hgl x y)
    _ = (C+D)*‖x-y‖ := by ring

theorem BoundedLipschitz.map_linear {f : E → F} (hf : BoundedLipschitz f)
    (L : F →L[ℝ] G) : BoundedLipschitz (fun x => L (f x)) := by
  obtain ⟨C,hC,hf,hfl⟩ := hf
  refine ⟨‖L‖*C, mul_nonneg (norm_nonneg _) hC, ?_, ?_⟩
  · intro x
    exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hf x) (norm_nonneg _))
  · intro x y
    rw [← map_sub]
    exact (L.le_opNorm _).trans (by calc
      ‖L‖*‖f x-f y‖ ≤ ‖L‖*(C*‖x-y‖) := mul_le_mul_of_nonneg_left (hfl x y) (norm_nonneg _)
      _ = _ := by ring)

theorem BoundedLipschitz.comp_linear {f : F → G} (hf : BoundedLipschitz f)
    (L : E →L[ℝ] F) : BoundedLipschitz (f ∘ L) := by
  obtain ⟨C,hC,hf,hfl⟩ := hf
  refine ⟨C*(1+‖L‖), by positivity, ?_, ?_⟩
  · intro x
    exact (hf _).trans (by nlinarith [norm_nonneg L])
  · intro x y
    change ‖f (L x)-f (L y)‖ ≤ _
    calc
      _ ≤ C*‖L x-L y‖ := hfl _ _
      _ = C*‖L (x-y)‖ := by rw [map_sub]
      _ ≤ C*(‖L‖*‖x-y‖) := mul_le_mul_of_nonneg_left (L.le_opNorm _) hC
      _ ≤ C*(1+‖L‖)*‖x-y‖ := by nlinarith [mul_nonneg hC (norm_nonneg (x-y))]

theorem BoundedLipschitz.bilinear {f : E → F} {g : E → G}
    (hf : BoundedLipschitz f) (hg : BoundedLipschitz g)
    (B : F →L[ℝ] G →L[ℝ] H) : BoundedLipschitz (fun x => B (f x) (g x)) := by
  obtain ⟨C,hC,hf,hfl⟩ := hf
  obtain ⟨D,hD,hg,hgl⟩ := hg
  refine ⟨2*‖B‖*C*D, by positivity, ?_, ?_⟩
  · intro x
    calc
      ‖B (f x) (g x)‖ ≤ ‖B‖*‖f x‖*‖g x‖ := B.le_opNorm₂ _ _
      _ ≤ ‖B‖*C*D := by gcongr; exact hf x; exact hg x
      _ ≤ 2*‖B‖*C*D := by nlinarith [mul_nonneg (mul_nonneg (norm_nonneg B) hC) hD]
  · intro x y
    have he : B (f x) (g x)-B (f y) (g y) =
        B (f x-f y) (g x)+B (f y) (g x-g y) := by
      simp only [map_sub, ContinuousLinearMap.sub_apply]
      abel
    rw [he]
    calc
      _ ≤ ‖B (f x-f y) (g x)‖+‖B (f y) (g x-g y)‖ := norm_add_le _ _
      _ ≤ ‖B‖*‖f x-f y‖*‖g x‖+‖B‖*‖f y‖*‖g x-g y‖ :=
        add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _)
      _ ≤ ‖B‖*(C*‖x-y‖)*D+‖B‖*C*(D*‖x-y‖) := by
        gcongr
        · exact hfl x y
        · exact hg x
        · exact hf y
        · exact hgl x y
      _ = (2*‖B‖*C*D)*‖x-y‖ := by ring

theorem boundedLipschitz_of_derivative_bound {f : E → F} (hf : Differentiable ℝ f)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hb : ∀ x, ‖f x‖ ≤ C)
    (hd : ∀ x, ‖fderiv ℝ f x‖ ≤ D) : BoundedLipschitz f := by
  refine ⟨C+D, add_nonneg hC hD, fun x => (hb x).trans (le_add_of_nonneg_right hD), ?_⟩
  intro x y
  have hl := Convex.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hf z)
    (fun z _ => hd z) (convex_univ : Convex ℝ (Set.univ : Set E)) (Set.mem_univ y) (Set.mem_univ x)
  exact hl.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC) (norm_nonneg _))

end
end SecondOrder
