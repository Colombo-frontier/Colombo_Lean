import SecondOrder.OjaDirections
import SecondOrder.FiniteCandidate

open MeasureTheory Filter
open scoped BigOperators InnerProductSpace Classical

namespace SecondOrder
noncomputable section

def ojaCandidateLaw {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (d N : ℕ) (hN : 0 < N) :
    Measure ((Draws Ω N × (Fin d → Bool)) × Fin N) := by
  letI : NeZero N := ⟨hN.ne'⟩
  exact (ojaRandomLaw μ d N).prod (PMF.uniformOfFintype (Fin N)).toMeasure

instance ojaCandidateLaw_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (d N : ℕ) (hN : 0 < N) :
    IsProbabilityMeasure (ojaCandidateLaw μ d N hN) := by
  unfold ojaCandidateLaw
  infer_instance

/-- Select one of the actual query directions uniformly and independently
of the loss samples and of the sign initialization. -/
def ojaCandidate {Ω : Type*} {d : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (η : ℝ) (x : Point d) (N : ℕ) (w : (Draws Ω N × (Fin d → Bool)) × Fin N) : Point d :=
  ojaDirections P f η x (rademacherInit w.1.2) N w.1.1 w.2

def ojaCandidateTrace {Ω : Type*} {d : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (η : ℝ) (x : Point d) (N : ℕ) (w : (Draws Ω N × (Fin d → Bool)) × Fin N) :
    List (Ω × HvpQuery d) := ojaRandomTrace P f η x N w.1

theorem ojaCandidateTrace_length {Ω : Type*} {d : ℕ} (P : Parameters)
    (f : Ω → Point d → ℝ) (η : ℝ) (x : Point d) (N : ℕ)
    (w : (Draws Ω N × (Fin d → Bool)) × Fin N) :
    (ojaCandidateTrace P f η x N w).length = N := ojaRandomTrace_length P f η x N w.1

theorem ojaDirections_mem_trace {Ω : Type*} {d : ℕ} (P : Parameters)
    (f : Ω → Point d → ℝ) (η : ℝ) (x v : Point d) (N : ℕ) (w : Draws Ω N) (i : Fin N) :
    ∃ z, (z,HvpQuery.hvp x (ojaDirections P f η x v N w i)) ∈ ojaHvpTrace P f η x v N w := by
  induction N with
  | zero => exact Fin.elim0 i
  | succ N ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · refine ⟨w.2,?_⟩
      simp [ojaDirections,ojaHvpTrace,ojaHvpQuery]
    · obtain ⟨z,hz⟩ := ih w.1 j
      refine ⟨z,?_⟩
      simp only [ojaDirections,Fin.snoc_castSucc,ojaHvpTrace,List.mem_append]
      exact Or.inl hz

theorem ojaCandidate_mem_trace {Ω : Type*} {d : ℕ} (P : Parameters)
    (f : Ω → Point d → ℝ) (η : ℝ) (x : Point d) (N : ℕ)
    (w : (Draws Ω N × (Fin d → Bool)) × Fin N) :
    ∃ z, (z,HvpQuery.hvp x (ojaCandidate P f η x N w)) ∈ ojaCandidateTrace P f η x N w :=
  ojaDirections_mem_trace P f η x (rademacherInit w.1.2) N w.1.1 w.2

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.ojaCandidate_measurable (h : CommonLoss μ P ν F f) (η : ℝ) (N : ℕ) :
    Measurable (fun w : Point d × ((Draws Ω N × (Fin d → Bool)) × Fin N) =>
      ojaCandidate P f η w.1 N w.2) := by
  have hi : Measurable (fun w : Point d × (Draws Ω N × (Fin d → Bool)) =>
      ((w.1,rademacherInit w.2.2),w.2.1)) :=
    (measurable_fst.prodMk ((rademacherInit_measurable d).comp measurable_snd.snd)).prodMk
      measurable_snd.fst
  have hm : Measurable (fun w : (Point d × (Draws Ω N × (Fin d → Bool))) × Fin N =>
      ojaDirections P f η w.1.1 (rademacherInit w.1.2.2) N w.1.2.1 w.2) := by
    apply measurable_from_prod_countable
    intro i
    exact ((measurable_pi_apply i).comp (h.ojaDirections_measurable η N)).comp hi
  exact hm.comp ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd)

theorem CommonLoss.ojaCandidate_ae_norm (h : CommonLoss μ P ν F f) (hd : 0 < d)
    {η : ℝ} (hη : 0 ≤ η) (N : ℕ) (hN : 0 < N) :
    ∀ᵐ w ∂ojaCandidateLaw μ d N hN, ∀ x : Point d, ‖ojaCandidate P f η x N w‖ = 1 := by
  letI : NeZero N := ⟨hN.ne'⟩
  have hp := (Measure.quasiMeasurePreserving_fst (μ := drawsLaw μ N) (ν := signLaw d)).ae
    (h.ojaDirections_ae_norm hη N)
  have hq := (Measure.quasiMeasurePreserving_fst (μ := ojaRandomLaw μ d N)
    (ν := (PMF.uniformOfFintype (Fin N)).toMeasure)).ae hp
  filter_upwards [hq] with w hw
  intro x
  exact hw x (rademacherInit w.1.2) (rademacherInit_norm hd w.1.2) w.2

/-- The implemented candidate is a unit vector whose population Rayleigh
value is within ε/2 of the maximum, with probability at least 1/96. -/
theorem CommonLoss.oja_candidate_accuracy (h : CommonLoss μ P ν F f) (hd : 0 < d)
    {ε : ℝ} (hε : 0 < ε) (x : Point d) :
    (1:ℝ)/96 ≤ (ojaCandidateLaw μ d (ojaIterationCount d ε) (ojaIterationCount_pos hd hε)).real
      {w | ‖ojaCandidate P f (ojaLearningRate d ε) x (ojaIterationCount d ε) w‖ = 1 ∧
        topRayleigh (shiftedHessian (eigenHessianBound P) (hessian F x)) - ε/2 ≤
          ⟪shiftedHessian (eigenHessianBound P) (hessian F x)
            (ojaCandidate P f (ojaLearningRate d ε) x (ojaIterationCount d ε) w),
              ojaCandidate P f (ojaLearningRate d ε) x (ojaIterationCount d ε) w⟫_ℝ} := by
  let N := ojaIterationCount d ε
  let η := ojaLearningRate d ε
  let ℓ := topRayleigh (shiftedHessian (eigenHessianBound P) (hessian F x))
  have hN : 0 < N := ojaIterationCount_pos hd hε
  have hN' : (0:ℝ) < N := Nat.cast_pos.mpr hN
  letI : NeZero N := ⟨hN.ne'⟩
  let ρ : Measure (Fin N) := (PMF.uniformOfFintype (Fin N)).toMeasure
  let G : Set (Draws Ω N × (Fin d → Bool)) :=
    {w | (ℓ-ε/4)*(N:ℝ) ≤ ojaRandomMeanRayleighSum P F f η x N w}
  let S : Set ((Draws Ω N × (Fin d → Bool)) × Fin N) :=
    {w | ‖ojaCandidate P f η x N w‖ = 1 ∧ ℓ-ε/2 ≤
      ⟪shiftedHessian (eigenHessianBound P) (hessian F x) (ojaCandidate P f η x N w),
        ojaCandidate P f η x N w⟫_ℝ}
  have hmi : Measurable (fun w : Draws Ω N × (Fin d → Bool) => (x,w)) :=
    measurable_const.prodMk measurable_id
  have hm : Measurable (fun w => ojaRandomMeanRayleighSum P F f η x N w) :=
    Measurable.comp
      (g := fun w : Point d × (Draws Ω N × (Fin d → Bool)) => ojaRandomMeanRayleighSum P F f η w.1 N w.2)
      (f := fun w : Draws Ω N × (Fin d → Bool) => (x,w)) (h.ojaRandomMeanRayleighSum_measurable η N) hmi
  have hG : MeasurableSet G := measurableSet_le measurable_const hm
  have hui : Measurable (fun w : (Draws Ω N × (Fin d → Bool)) × Fin N => (x,w)) :=
    measurable_const.prodMk measurable_id
  have hu : Measurable (ojaCandidate P f η x N) := (h.ojaCandidate_measurable η N).comp hui
  have hq : Measurable (fun w => ⟪shiftedHessian (eigenHessianBound P) (hessian F x)
      (ojaCandidate P f η x N w),ojaCandidate P f η x N w⟫_ℝ) :=
    ((shiftedHessian (eigenHessianBound P) (hessian F x)).continuous.inner continuous_id).measurable
      |>.comp hu
  have hS : MeasurableSet S :=
    (measurableSet_eq_fun hu.norm measurable_const).inter (measurableSet_le measurable_const hq)
  have htop := (h.mean_shifted_top_eigenpair hd x).2.2.1
  have hn := (Measure.quasiMeasurePreserving_fst (μ := drawsLaw μ N) (ν := signLaw d)).ae
    (h.ojaDirections_ae_norm (ojaLearningRate_pos hd hε).le N)
  have hsections : ∀ᵐ z ∂ojaRandomLaw μ d N, z ∈ G → (1:ℝ)/2 ≤ ρ.real {i | (z,i) ∈ S} := by
    filter_upwards [hn] with z hz
    intro hzg
    let R : Fin N → ℝ := fun i =>
      ⟪shiftedHessian (eigenHessianBound P) (hessian F x)
        (ojaDirections P f η x (rademacherInit z.2) N z.1 i),
          ojaDirections P f η x (rademacherInit z.2) N z.1 i⟫_ℝ
    have hunit (i : Fin N) : ‖ojaDirections P f η x (rademacherInit z.2) N z.1 i‖ = 1 :=
      hz x (rademacherInit z.2) (rademacherInit_norm hd z.2) i
    have hr (i : Fin N) : R i ≤ ℓ := by
      have hb := htop (ojaDirections P f η x (rademacherInit z.2) N z.1 i)
      simpa only [hunit i,one_pow,mul_one] using hb
    have hs : (∑ i, R i) = ojaRandomMeanRayleighSum P F f η x N z :=
      ojaDirections_mean_sum P F f η x (rademacherInit z.2) N z.1
    have havg : ℓ-ε/4 ≤ uniformMean R := by
      rw [uniformMean_eq,Fintype.card_fin,smul_eq_mul,hs]
      rw [mul_comm,← div_eq_mul_inv]
      exact (le_div_iff₀ hN').mpr hzg
    refine (uniform_candidate_probability R hε hr havg).trans ?_
    refine measureReal_mono ?_ (measure_ne_top _ _)
    intro i hi
    exact ⟨hunit i,hi⟩
  have hp := product_success_of_sections_ae (μ := ojaRandomLaw μ d N) (ρ := ρ) hG hS hsections
  have ha : (1:ℝ)/48 ≤ (ojaRandomLaw μ d N).real G := h.oja_average_accuracy hd hε x
  change (1:ℝ)/96 ≤ ((ojaRandomLaw μ d N).prod ρ).real S
  linarith

end
end SecondOrder
