import Geode.LogMap

/-! Global Riemannian support and normal-cone predicates in the concrete
hyperboloid. The Lorentz form restricted to tangent vectors is its metric. -/
namespace Geode.Lorentz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def IsSubgradient (f : Point E → ℝ) (x : Point E) (g : Ambient E) : Prop :=
  form E x.val g = 0 ∧ ∀ y, f x + form E g (logMap x y) ≤ f y

def NormalTo (K : Set (Point E)) (z : Point E) (n : Ambient E) : Prop :=
  form E z.val n = 0 ∧ ∀ x ∈ K, form E n (logMap z x) ≤ 0

theorem isSubgradient_zero_iff (f : Point E → ℝ) (x : Point E) :
    IsSubgradient f x 0 ↔ ∀ y, f x ≤ f y := by
  simp [IsSubgradient]

theorem IsSubgradient.const_mul {f : Point E → ℝ} {x : Point E} {g : Ambient E}
    (hg : IsSubgradient f x g) {a : ℝ} (ha : 0 ≤ a) :
    IsSubgradient (fun y => a * f y) x (a • g) := by
  constructor
  · simp [hg.1]
  · intro y
    simpa only [form_smul_left, mul_add] using mul_le_mul_of_nonneg_left (hg.2 y) ha

theorem IsSubgradient.add {f h : Point E → ℝ} {x : Point E} {g k : Ambient E}
    (hg : IsSubgradient f x g) (hk : IsSubgradient h x k) :
    IsSubgradient (fun y => f y + h y) x (g + k) := by
  constructor
  · simp [hg.1, hk.1]
  · intro y
    have hf := hg.2 y
    have hh := hk.2 y
    change f x + h x + form E (g + k) (logMap x y) ≤ f y + h y
    rw [form_add_left]
    linarith

theorem form_logMap_right {z : Point E} {n : Ambient E} (hn : form E z.val n = 0)
    (x : Point E) :
    form E n (logMap z x) = (dist z x / Real.sinh (dist z x)) * form E n x.val := by
  have hnz : form E n z.val = 0 := by rw [form_comm]; exact hn
  simp only [logMap, direction, form_smul_right, form_sub_right, hnz]
  ring

/-- The Riemannian normal cone is exactly the supporting Lorentz halfspace. -/
theorem normalTo_iff_lorentz_halfspace {K : Set (Point E)} {z : Point E} {n : Ambient E} :
    NormalTo K z n ↔ form E z.val n = 0 ∧ ∀ x ∈ K, form E n x.val ≤ 0 := by
  constructor
  · rintro ⟨hn, hs⟩
    refine ⟨hn, ?_⟩
    intro x hx
    by_cases hzx : z = x
    · subst x
      rw [form_comm, hn]
    · have hd : 0 < dist z x := dist_pos.mpr hzx
      have hp : 0 < dist z x / Real.sinh (dist z x) := div_pos hd (Real.sinh_pos_iff.mpr hd)
      have h := hs x hx
      rw [form_logMap_right hn] at h
      exact nonpos_of_mul_nonpos_right h hp
  · rintro ⟨hn, hs⟩
    refine ⟨hn, ?_⟩
    intro x hx
    rw [form_logMap_right hn]
    exact mul_nonpos_of_nonneg_of_nonpos
      (div_nonneg dist_nonneg (Real.sinh_nonneg_iff.mpr dist_nonneg)) (hs x hx)

theorem normalTo_zero (K : Set (Point E)) (z : Point E) : NormalTo K z 0 := by
  simp [NormalTo]

theorem NormalTo.mono {K C : Set (Point E)} {z : Point E} {n : Ambient E}
    (hn : NormalTo K z n) (hCK : C ⊆ K) : NormalTo C z n :=
  ⟨hn.1, fun x hx => hn.2 x (hCK hx)⟩

end Geode.Lorentz
