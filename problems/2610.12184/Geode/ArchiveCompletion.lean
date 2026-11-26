import Geode.PublicState
import Geode.ScaledObjective

/-! A consistent finite archive of persistent full contacts is realized by one
actual admissible objective and one fixed globally legal first-order oracle. -/

namespace Geode.Lorentz

open Geode.OracleReplay

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {o : Point E} {R μ L : ℝ}

def ArchiveValid (s : PublicState o R μ)
    (history : History (Point E) (FirstOrderReply E)) (L : ℝ) : Prop :=
  Consistent history ∧ ∀ y r, (y, r) ∈ history →
    ∃ a : ArchivedContact E, a.y = y ∧ a.reply μ L = r ∧ ContactSupports s a

theorem ArchiveValid.nil (s : PublicState o R μ) (L : ℝ) : ArchiveValid s [] L := by
  constructor
  · intro x r r' hr
    simp only [List.not_mem_nil] at hr
  · intro y r hr
    simp only [List.not_mem_nil] at hr

theorem ArchiveValid.extend [FiniteDimensional ℝ E] {s s' : PublicState o R μ}
    {history : History (Point E) (FirstOrderReply E)} (h : ArchiveValid s history L)
    (he : StateExtension s s') : ArchiveValid s' history L := by
  refine ⟨h.1, ?_⟩
  intro y r hr
  obtain ⟨a, hy, hr, ha⟩ := h.2 y r hr
  exact ⟨a, hy, hr, ha.extend he⟩

theorem ArchiveValid.append_fresh {s : PublicState o R μ}
    {history : History (Point E) (FirstOrderReply E)} (h : ArchiveValid s history L)
    (a : ArchivedContact E) (ha : ContactSupports s a)
    (hfresh : ∀ r, (a.y, r) ∉ history) :
    ArchiveValid s (history ++ [(a.y, a.reply μ L)]) L := by
  constructor
  · intro x r r' hr hr'
    simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at hr hr'
    rcases hr with hr | ⟨rfl, rfl⟩
    · rcases hr' with hr' | ⟨rfl, rfl⟩
      · exact h.1 x r r' hr hr'
      · exact (hfresh r hr).elim
    · rcases hr' with hr' | ⟨_, rfl⟩
      · exact (hfresh r' hr').elim
      · rfl
  · intro y r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact h.2 y r hr
    · have heq := List.mem_singleton.mp hr
      cases heq
      exact ⟨a, rfl, rfl, ha⟩

theorem ArchiveValid.append_cached {s : PublicState o R μ}
    {history : History (Point E) (FirstOrderReply E)} (h : ArchiveValid s history L)
    {y : Point E} {r : FirstOrderReply E} (hr : (y, r) ∈ history) :
    ArchiveValid s (history ++ [(y, r)]) L := by
  have hmem : ∀ e, e ∈ history ++ [(y, r)] → e ∈ history := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact he
    · simpa only [List.mem_singleton.mp he] using hr
  exact ⟨fun x r₁ r₂ h₁ h₂ => h.1 x r₁ r₂ (hmem _ h₁) (hmem _ h₂),
    fun x r' hr' => h.2 x r' (hmem _ hr')⟩

def completionCarrier (s : PublicState o R μ) (p : Point E) : Set (Point E) :=
  closedGConv (s.P ∪ {p})

noncomputable def completionObjective (s : PublicState o R μ) (p : Point E) (L : ℝ) :
    Point E → ℝ := scaledObjective L (Geode.carrierValue (completionCarrier s p) p μ)

theorem completionCarrier_compact [FiniteDimensional ℝ E] (s : PublicState o R μ) (p : Point E) :
    IsCompact (completionCarrier s p) :=
  isCompact_closedGConv_of_bounded (s.compact.union isCompact_singleton).isBounded

theorem completionCarrier_convex (s : PublicState o R μ) (p : Point E) :
    GConvex (completionCarrier s p) := gconvex_closedGConv _

theorem mem_completionCarrier (s : PublicState o R μ) (p : Point E) :
    p ∈ completionCarrier s p := subset_closedGConv _ (Or.inr rfl)

theorem ContactSupports.normal_completion {s : PublicState o R μ}
    {a : ArchivedContact E} (ha : ContactSupports s a) {p : Point E}
    (hp : p ∈ s.candidates) : NormalTo (completionCarrier s p) a.z (a.normal μ p) := by
  apply normalTo_iff_lorentz_halfspace.mpr
  refine ⟨(ha.normal p hp).1, ?_⟩
  apply closedGConv_subset_halfspace (a.normal μ p)
  intro x hx
  rcases hx with hx | hx
  · exact (normalTo_iff_lorentz_halfspace.mp (ha.normal p hp)).2 x hx
  · have hxp : x = p := Set.mem_singleton_iff.mp hx
    subst x
    exact (ha.strict p hp).le

theorem ContactSupports.realizes_contact {s : PublicState o R μ}
    {a : ArchivedContact E} (ha : ContactSupports s a) {p : Point E}
    (hp : p ∈ s.candidates) (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    Geode.carrierValue (completionCarrier s p) p μ a.y = μ * a.D + dist a.y a.z ∧
      IsSubgradient (Geode.carrierValue (completionCarrier s p) p μ) a.y a.gradient := by
  have hz : a.z ∈ completionCarrier s p := subset_closedGConv _ (Or.inl ha.contact_mem)
  have hd := ha.distance p hp
  have hzp : a.z ≠ p := by
    intro heq
    have hdist : dist a.z p = 0 := dist_eq_zero.mpr heq
    linarith [a.positive]
  have hn := ha.normal_completion hp
  by_cases hy : a.y = a.z
  · obtain ⟨hv, hg⟩ := carrier_internal_contact hz hμ hμ1 hzp a.tangent a.unit hn
    refine ⟨?_, ?_⟩
    · simpa only [hy, dist_self, add_zero, hd] using hv
    · simpa only [ArchivedContact.gradient, if_pos hy, hy] using hg
  · obtain ⟨hv, hg⟩ := carrier_external_contact hz hμ hzp hy (a.direction_eq hy) hn
    exact ⟨by simpa only [hd] using hv,
      by simpa only [ArchivedContact.gradient, if_neg hy] using hg⟩

theorem ContactSupports.realizes_reply {s : PublicState o R μ}
    {a : ArchivedContact E} (ha : ContactSupports s a) {p : Point E}
    (hp : p ∈ s.candidates) (hL : 0 ≤ L) (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    (a.reply μ L).1 = completionObjective s p L a.y ∧
      IsSubgradient (completionObjective s p L) a.y (a.reply μ L).2 := by
  obtain ⟨hv, hg⟩ := ha.realizes_contact hp hμ hμ1
  exact ⟨congrArg (fun v : ℝ => L * v) hv.symm, hg.const_mul hL⟩

theorem completionObjective_admissible [FiniteDimensional ℝ E] (s : PublicState o R μ) {p : Point E}
    (hp : p ∈ s.candidates) (hL : 0 ≤ L) (hμ : 0 < μ) (hμ1 : μ < 1) :
    AdmissibleObjective o R L (completionObjective s p L) :=
  scaled_carrier_admissible (completionCarrier_compact s p) (completionCarrier_convex s p)
    (mem_completionCarrier s p) (s.original p hp).le hL hμ hμ1

/-- The finite archive has a single globally legal fixed completion. -/
theorem ArchiveValid.complete_explicit [FiniteDimensional ℝ E] {s : PublicState o R μ}
    {history : History (Point E) (FirstOrderReply E)} (h : ArchiveValid s history L)
    {p : Point E} (hp : p ∈ s.candidates) (hL : 0 < L) (hμ : 0 < μ) (hμ1 : μ < 1) :
    ∃ O : Point E → FirstOrderReply E,
      AdmissibleObjective o R L (completionObjective s p L) ∧
      LegalOracle (completionObjective s p L) O ∧
      (∀ y r, (y, r) ∈ history → O y = r) ∧
      (∀ x, (∀ y, completionObjective s p L x ≤ completionObjective s p L y) ↔ x = p) ∧
      completionObjective s p L p = 0 ∧
      (∀ y, L * μ * dist y p ≤ completionObjective s p L y) := by
  let fallback := scaledOracle L (carrierOracle (p := p) (completionCarrier_compact s p)
    (completionCarrier_convex s p) ⟨p, mem_completionCarrier s p⟩ hμ.le hμ1.le)
  have hfallback : LegalOracle (completionObjective s p L) fallback :=
    scaled_carrierOracle_legal (completionCarrier_compact s p) (completionCarrier_convex s p)
      ⟨p, mem_completionCarrier s p⟩ hL.le hμ.le hμ1.le
  have harchive : ∀ y r, (y, r) ∈ history →
      r.1 = completionObjective s p L y ∧ IsSubgradient (completionObjective s p L) y r.2 := by
    intro y r hr
    obtain ⟨a, rfl, rfl, ha⟩ := h.2 y r hr
    exact ha.realizes_reply hp hL.le hμ.le hμ1.le
  refine ⟨cachedOracle history fallback, completionObjective_admissible s hp hL.le hμ hμ1,
    cachedOracle_legal history fallback _ harchive hfallback,
    fun y r hr => cachedOracle_realizes history fallback h.1 hr, ?_, ?_, ?_⟩
  · exact scaled_carrier_unique_minimizer (mem_completionCarrier s p) hL hμ hμ1.le
  · exact scaled_carrier_at_center (mem_completionCarrier s p) hμ.le hμ1.le
  · intro y
    exact scaled_carrier_floor ⟨p, mem_completionCarrier s p⟩ hL.le hμ.le hμ1.le

theorem ArchiveValid.complete [FiniteDimensional ℝ E] {s : PublicState o R μ}
    {history : History (Point E) (FirstOrderReply E)} (h : ArchiveValid s history L)
    {p : Point E} (hp : p ∈ s.candidates) (hL : 0 < L) (hμ : 0 < μ) (hμ1 : μ < 1) :
    ∃ (f : Point E → ℝ) (O : Point E → FirstOrderReply E),
      AdmissibleObjective o R L f ∧ LegalOracle f O ∧
      (∀ x, (∀ y, f x ≤ f y) ↔ x = p) ∧ f p = 0 ∧
      (∀ x, L * μ * dist x p ≤ f x) ∧
      (∀ y r, (y, r) ∈ history → O y = r) := by
  obtain ⟨O, hf, hO, harchive, hmin, hzero, hfloor⟩ :=
    h.complete_explicit hp hL hμ hμ1
  exact ⟨completionObjective s p L, O, hf, hO, hmin, hzero, hfloor, harchive⟩

end Geode.Lorentz
