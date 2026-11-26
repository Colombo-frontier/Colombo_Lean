import Geode.SubgradientBounds
import Geode.TangentTopology
import Geode.OracleModel
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Convex.Basic

/-! Closedness, convexity, compactness, and the unique minimum-norm point
of the actual global subdifferential. Nonemptiness is kept explicit here
so the general existence proof can import this module without a cycle. -/
namespace Geode.Lorentz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def subdifferential (f : Point E → ℝ) (x : Point E) : Set (Ambient E) :=
  {g | IsSubgradient f x g}

@[simp] theorem mem_subdifferential (f : Point E → ℝ) (x : Point E) (g : Ambient E) :
    g ∈ subdifferential f x ↔ IsSubgradient f x g := Iff.rfl

theorem subdifferential_closed (f : Point E → ℝ) (x : Point E) :
    IsClosed (subdifferential f x) := by
  have hs : subdifferential f x =
      {g : Ambient E | form E x.val g = 0} ∩
        ⋂ y : Point E, {g : Ambient E | f x + form E g (logMap x y) ≤ f y} := by
    ext g
    simp only [subdifferential, IsSubgradient, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_setOf_eq]
  rw [hs]
  exact (isClosed_eq (continuous_form_right x.val) continuous_const).inter
    (isClosed_iInter fun y =>
      isClosed_le (continuous_const.add (continuous_form_left (logMap x y))) continuous_const)

theorem subdifferential_convex (f : Point E → ℝ) (x : Point E) :
    Convex ℝ (subdifferential f x) := by
  intro u hu v hv a b ha hb hab
  refine ⟨by simp [hu.1, hv.1], ?_⟩
  intro y
  simp only [form_add_left, form_smul_left]
  have hau := mul_le_mul_of_nonneg_left (hu.2 y) ha
  have hbv := mul_le_mul_of_nonneg_left (hv.2 y) hb
  have hfx := congrArg (fun t : ℝ => t * f x) hab
  have hfy := congrArg (fun t : ℝ => t * f y) hab
  dsimp only at hfx hfy
  nlinarith only [hau, hbv, hfx, hfy]

theorem subdifferential_subset_tangent_ball {f : Point E → ℝ} (x : Point E)
    {L : ℝ} (hL : 0 ≤ L) (hlip : ∀ a b, |f a - f b| ≤ L * dist a b) :
    subdifferential f x ⊆ {g | form E x.val g = 0 ∧ tangentNorm g ≤ L} := by
  intro g hg
  exact ⟨hg.1, subgradient_norm_le hL hlip hg⟩

theorem subdifferential_ambient_norm_le {f : Point E → ℝ} {x : Point E}
    {L : ℝ} (hL : 0 ≤ L) (hlip : ∀ a b, |f a - f b| ≤ L * dist a b)
    {g : Ambient E} (hg : g ∈ subdifferential f x) : ‖g‖ ≤ x.val.1 * L :=
  (ambient_norm_le_tangent x hg.1).trans
    (mul_le_mul_of_nonneg_left (subgradient_norm_le hL hlip hg) x.future.le)

theorem subdifferential_bounded {f : Point E → ℝ} (x : Point E)
    {L : ℝ} (hL : 0 ≤ L) (hlip : ∀ a b, |f a - f b| ≤ L * dist a b) :
    Bornology.IsBounded (subdifferential f x) := by
  apply isBounded_iff_forall_norm_le.mpr
  exact ⟨x.val.1 * L, fun _ hg => subdifferential_ambient_norm_le hL hlip hg⟩

theorem subgradient_minimum_unique {f : Point E → ℝ} {x : Point E}
    {g h : Ambient E} (hg : IsSubgradient f x g) (hh : IsSubgradient f x h)
    (hgm : ∀ v, IsSubgradient f x v → tangentNorm g ≤ tangentNorm v)
    (hhm : ∀ v, IsSubgradient f x v → tangentNorm h ≤ tangentNorm v) : g = h := by
  let m : Ambient E := (1 / 2 : ℝ) • g + (1 / 2 : ℝ) • h
  have hm : IsSubgradient f x m :=
    subdifferential_convex f x hg hh (by norm_num) (by norm_num) (by norm_num)
  have hsqg : tangentNorm g ^ 2 = form E g g := Real.sq_sqrt (tangent_nonneg x hg.1)
  have hsqh : tangentNorm h ^ 2 = form E h h := Real.sq_sqrt (tangent_nonneg x hh.1)
  have hsqm : tangentNorm m ^ 2 = form E m m := Real.sq_sqrt (tangent_nonneg x hm.1)
  have heq : tangentNorm g = tangentNorm h := le_antisymm (hgm h hh) (hhm g hg)
  have hforms : form E g g = form E h h := by rw [← hsqg, ← hsqh, heq]
  have hmid : form E g g ≤ form E m m := by
    rw [← hsqg, ← hsqm]
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).mpr (hgm m hm)
  have ht : form E x.val (g - h) = 0 := by simp [hg.1, hh.1]
  have hnonneg := tangent_nonneg x ht
  have hcomm : form E h g = form E g h := form_comm h g
  have hdiff : form E (g - h) (g - h) = 0 := by
    simp only [m, form_add_left, form_add_right, form_smul_left, form_smul_right,
      hcomm] at hmid
    simp only [form_sub_left, form_sub_right, hcomm] at hnonneg ⊢
    linarith only [hmid, hforms, hnonneg]
  exact sub_eq_zero.mp ((tangent_eq_zero_iff x ht).mp hdiff)

variable [FiniteDimensional ℝ E]

theorem subdifferential_compact {f : Point E → ℝ} (x : Point E)
    {L : ℝ} (hL : 0 ≤ L) (hlip : ∀ a b, |f a - f b| ≤ L * dist a b) :
    IsCompact (subdifferential f x) :=
  Metric.isCompact_of_isClosed_isBounded (subdifferential_closed f x)
    (subdifferential_bounded x hL hlip)

theorem subdifferential_unique_minimum {f : Point E → ℝ} (x : Point E)
    {L : ℝ} (hL : 0 ≤ L) (hlip : ∀ a b, |f a - f b| ≤ L * dist a b)
    (hne : ∃ g, IsSubgradient f x g) :
    ∃! g : Ambient E, IsSubgradient f x g ∧
      ∀ v, IsSubgradient f x v → tangentNorm g ≤ tangentNorm v := by
  obtain ⟨g, hg, hmin⟩ := (subdifferential_compact x hL hlip).exists_isMinOn hne
    continuous_tangentNorm.continuousOn
  refine ⟨g, ⟨hg, hmin⟩, ?_⟩
  intro h hh
  exact subgradient_minimum_unique hh.1 hg hh.2 hmin

noncomputable def minimumNormSubgradient {f : Point E → ℝ} (x : Point E)
    {L : ℝ} (hL : 0 ≤ L) (hlip : ∀ a b, |f a - f b| ≤ L * dist a b)
    (hne : ∃ g, IsSubgradient f x g) : Ambient E :=
  Classical.choose (subdifferential_unique_minimum x hL hlip hne)

theorem minimumNormSubgradient_spec {f : Point E → ℝ} (x : Point E)
    {L : ℝ} (hL : 0 ≤ L) (hlip : ∀ a b, |f a - f b| ≤ L * dist a b)
    (hne : ∃ g, IsSubgradient f x g) :
    IsSubgradient f x (minimumNormSubgradient x hL hlip hne) ∧
      ∀ v, IsSubgradient f x v → tangentNorm (minimumNormSubgradient x hL hlip hne) ≤
        tangentNorm v :=
  (Classical.choose_spec (subdifferential_unique_minimum x hL hlip hne)).1

noncomputable def minimumNormOracle (f : Point E → ℝ) {L : ℝ}
    (hL : 0 ≤ L) (hlip : ∀ a b, |f a - f b| ≤ L * dist a b)
    (hne : ∀ x, ∃ g, IsSubgradient f x g) : Point E → FirstOrderReply E :=
  fun x => (f x, minimumNormSubgradient x hL hlip (hne x))

theorem minimumNormOracle_legal (f : Point E → ℝ) {L : ℝ}
    (hL : 0 ≤ L) (hlip : ∀ a b, |f a - f b| ≤ L * dist a b)
    (hne : ∀ x, ∃ g, IsSubgradient f x g) :
    LegalOracle f (minimumNormOracle f hL hlip hne) :=
  fun x => ⟨rfl, (minimumNormSubgradient_spec x hL hlip (hne x)).1⟩

end Geode.Lorentz
