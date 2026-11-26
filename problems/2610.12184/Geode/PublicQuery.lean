import Geode.GeometricRouting
import Geode.PublicContactOptimality
import Geode.LorentzProjection

/-! Construction of public routing data for actual arbitrary query points.
A unit residual vector is an explicit dimension-theoretic input. -/
namespace Geode.Lorentz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem logMap_mem_section (W : Submodule ℝ (Ambient E)) {z x : Point E}
    (hz : z.val ∈ W) (hx : x.val ∈ W) : logMap z x ∈ W :=
  W.smul_mem _ (W.smul_mem _ (W.sub_mem hx (W.smul_mem _ hz)))

theorem on_domain_routing_exists {P : Set (Point E)} (W : Submodule ℝ (Ambient E))
    (c y : Point E) {μ S : ℝ} (hμ : 0 < μ) (hμmax : μ ≤ 1 / 16) (hS : 0 < S)
    (hc : c.val ∈ W) (hy : y ∈ P) (hsection : ∀ x ∈ P, x.val ∈ W)
    (hball : ∀ x : Point E, x.val ∈ W → dist c x ≤ publicRadius (Geode.eta μ) S → x ∈ P)
    (e : Ambient E) (he : ∀ w ∈ W, form E e w = 0) (heunit : form E e e = 1) :
    ∃ C : RoutingData P W c y μ S,
      0 < C.β ∧ C.qV = (-μ) • publicDirection c y S ∧ C.e = e := by
  have hyW := hsection y hy
  have hey : form E y.val e = 0 := by rw [form_comm]; exact he _ hyW
  have heu : form E (publicDirection c y S) e = 0 := by
    rw [form_comm]
    exact he _ (publicDirection_mem c y S W hc hyW)
  have hu1 : form E (publicDirection c y S) (publicDirection c y S) ≤ 1 := by
    rw [publicDirection_form_self c y hS]
    have : 0 ≤ 1 / publicRatio c y S ^ 2 := by positivity
    linarith
  have hμ1 : μ < 1 := by linarith
  obtain ⟨hb, hqt, hqn⟩ := on_domain_contact_direction (publicDirection_tangent c y S)
    hey heunit heu hu1 hμ.le hμ1
  let β := Real.sqrt (1 - μ ^ 2 * form E (publicDirection c y S) (publicDirection c y S))
  let qV := (-μ) • publicDirection c y S
  have hn : publicNormal c y qV μ S = 0 := by
    unfold publicNormal qV
    module
  let C : RoutingData P W c y μ S := {
    q := qV + β • e
    qV := qV
    e := e
    β := β
    center_mem := hc
    contact_mem := hyW
    carrier_section := hsection
    contains_ball := hball
    q_tangent := hqt
    q_unit := hqn
    public_mem := W.smul_mem _ (publicDirection_mem c y S W hc hyW)
    residual_orthogonal := he
    residual_unit := heunit
    decomposition := rfl
    beta_nonneg := hb.le
    normal := by rw [hn]; exact normalTo_zero P y }
  exact ⟨C, hb, rfl, rfl⟩

variable [FiniteDimensional ℝ E]

theorem publicPart_pairing (W : Submodule ℝ (Ambient E)) {c : Point E}
    (hc : c.val ∈ W) (q w : Ambient E) (hw : w ∈ W) :
    form E (publicPart W c q) w = form E q w := by
  have h := congrArg (fun u => form E u w) (publicPart_add_residualPart W c q)
  simpa only [form_add_left, residualPart_orthogonal W hc q hw, add_zero] using h

theorem routingData_of_direction {P : Set (Point E)} (W : Submodule ℝ (Ambient E))
    (c z : Point E) {μ S : ℝ} (hc : c.val ∈ W) (hz : z.val ∈ W)
    (hsection : ∀ x ∈ P, x.val ∈ W)
    (hball : ∀ x : Point E, x.val ∈ W → dist c x ≤ publicRadius (Geode.eta μ) S → x ∈ P)
    (q : Ambient E) (hqt : form E z.val q = 0) (hqu : form E q q = 1)
    (hn : NormalTo P z (publicNormal c z (publicPart W c q) μ S))
    (e₀ : Ambient E) (he₀ : ∀ w ∈ W, form E e₀ w = 0) (he₀unit : form E e₀ e₀ = 1) :
    ∃ C : RoutingData P W c z μ S, C.q = q ∧ C.qV = publicPart W c q := by
  by_cases hr : residualPart W c q = 0
  · have hdecomp : q = publicPart W c q + (0 : ℝ) • e₀ := by
      have h := publicPart_add_residualPart W c q
      simpa only [hr, zero_smul, add_zero] using h.symm
    exact ⟨{
      q := q, qV := publicPart W c q, e := e₀, β := 0,
      center_mem := hc, contact_mem := hz, carrier_section := hsection, contains_ball := hball,
      q_tangent := hqt, q_unit := hqu, public_mem := publicPart_mem W hc q,
      residual_orthogonal := he₀, residual_unit := he₀unit,
      decomposition := hdecomp, beta_nonneg := le_rfl, normal := hn }, rfl, rfl⟩
  · exact ⟨{
      q := q, qV := publicPart W c q, e := residualUnit W c q, β := residualSize W c q,
      center_mem := hc, contact_mem := hz, carrier_section := hsection, contains_ball := hball,
      q_tangent := hqt, q_unit := hqu, public_mem := publicPart_mem W hc q,
      residual_orthogonal := fun w hw => residualUnit_orthogonal W hc q hw,
      residual_unit := residualUnit_unit W hc hr,
      decomposition := public_residual_decomposition W hc hr,
      beta_nonneg := (residualSize_pos W hc hr).le, normal := hn }, rfl, rfl⟩

theorem exterior_routing_exists {P : Set (Point E)} (W : Submodule ℝ (Ambient E))
    (c y : Point E) {μ S : ℝ} (hμ : 0 < μ) (hμmax : μ ≤ 1 / 16) (hS : 0 < S)
    (hPc : IsCompact P) (hP : GConvex P) (hc : c.val ∈ W) (hy : y ∉ P)
    (hsection : ∀ x ∈ P, x.val ∈ W)
    (hball : ∀ x : Point E, x.val ∈ W → dist c x ≤ publicRadius (Geode.eta μ) S → x ∈ P)
    (e₀ : Ambient E) (he₀ : ∀ w ∈ W, form E e₀ w = 0) (he₀unit : form E e₀ e₀ = 1) :
    ∃ z ∈ P, ∃ C : RoutingData P W c z μ S, C.q = direction z y ∧
      ∀ w ∈ P, μ * publicDistance c z S + dist y z ≤ μ * publicDistance c w S + dist y w := by
  have hec : form E c.val e₀ = 0 := by rw [form_comm]; exact he₀ _ hc
  let p := unitGeodesic c e₀ hec he₀unit S
  have hrep : p.val = Real.cosh S • c.val + Real.sinh S • e₀ := rfl
  have hpW : p.val ∉ W := by
    intro hp
    have h := he₀ _ hp
    rw [hrep, form_add_right, form_smul_right, form_smul_right, he₀ c.val hc, he₀unit] at h
    nlinarith [Real.sinh_pos_iff.mpr hS]
  have hp : p ∉ P := fun hpP => hpW (hsection p hpP)
  have hne : P.Nonempty := by
    refine ⟨c, hball c hc ?_⟩
    simpa only [dist_self] using publicRadius_nonneg (Geode.eta_pos hμ hμmax).le hS.le
  obtain ⟨z, hz, _hn, hmin⟩ := radial_contact_normal_exists hPc hP hne hμ.le hy hp
  have hzW := hsection z hz
  have hyz : y ≠ z := by intro h; apply hy; simpa only [h] using hz
  have hpz : p ≠ z := by intro h; apply hp; simpa only [h] using hz
  have hpublic : ∀ x ∈ P, dist x p = publicDistance c x S := by
    intro x hx
    exact residual_distance c x p e₀ S W (hsection x hx) he₀ hrep
  have hqpair : ∀ x ∈ P, form E (publicPart W c (direction z y)) (logMap z x) =
      form E (direction z y) (logMap z x) := by
    intro x hx
    exact publicPart_pairing W hc _ _ (logMap_mem_section W hzW (hsection x hx))
  have hupair : ∀ x ∈ P, form E (publicDirection c z S) (logMap z x) =
      form E (direction z p) (logMap z x) := by
    intro x hx
    rw [residual_direction c z p e₀ hS W hzW he₀ hrep, form_add_left, form_smul_left,
      he₀ _ (logMap_mem_section W hzW (hsection x hx)), mul_zero, add_zero]
  have hnormal := radial_contact_public_normal hP hz hyz hpz hmin
    (publicPart_tangent W hc hzW (direction_tangent z y)) (publicDirection_tangent c z S)
    hqpair hupair
  obtain ⟨C, hCq, _⟩ := routingData_of_direction W c z hc hzW hsection hball (direction z y)
    (direction_tangent z y) (direction_unit z y hyz.symm) hnormal e₀ he₀ he₀unit
  refine ⟨z, hz, C, hCq, ?_⟩
  intro w hw
  have h := hmin w hw
  rwa [hpublic z hz, hpublic w hw] at h

end Geode.Lorentz
