import Bilevel.PolishedLiteralSourceCoupling
import Bilevel.MultiscaleActivation
import Bilevel.BorelAdaptiveActivation

/-! The counter of the actual compiled literal virtual run is bounded by
the same iid Bernoulli stream's success count. The projection prior and
private state remain random and independent of that fresh stream. -/
noncomputable section
open MeasureTheory
namespace Bilevel.PolishedLiteralActualObserver
open EuclideanGaussian ProjectionPosterior
set_option autoImplicit false
variable {dx du Kx Ku : ℕ} {S Q O Y : Type}
  [MeasurableSpace S] [MeasurableSpace Q] [MeasurableSpace O] [MeasurableSpace Y]
  (Px : PrefixSchedule Kx) (Pu : PrefixSchedule Ku)
  (A : BorelAdaptive.Program S Q O Y)
  (reply : Frame dx Kx → Frame du Ku → Q → ℕ → Bool → O)

theorem masterRun_succ_last (draws : ℕ → Bool) (U : Frame dx Kx) (V : Frame du Ku) :
    ∀ n t s,masterRun Px Pu A reply draws U V (n+1) t s=
      masterStep Px Pu A reply draws U V (t+n) (masterRun Px Pu A reply draws U V n t s) := by
  intro n
  induction n with
  | zero => intros;rfl
  | succ n ih =>
    intro t s
    rw [masterRun,ih,masterRun]
    congr 1
    omega

theorem master_counter_le_draws (draws : ℕ → Bool) (U : Frame dx Kx) (V : Frame du Ku) (s : S) :
    ∀ n,((masterRun Px Pu A reply draws U V n 0 (s,0)).2:ℝ)≤
      MultiscaleActivation.count n (IndependentStream.project n draws) := by
  intro n
  induction n with
  | zero => simp [masterRun,MultiscaleActivation.count]
  | succ n ih =>
    rw [masterRun_succ_last]
    let z := masterRun Px Pu A reply draws U V n 0 (s,0)
    have hstep : ((masterStep Px Pu A reply draws U V n z).2:ℝ)≤
        (z.2:ℝ)+(if draws n then 1 else 0) := by
      by_cases hh : A.halt z.1=true
      · simp only [masterStep,if_pos hh]
        cases hc : draws n <;> simp [hc]
      · simp only [masterStep,if_neg hh]
        cases hc : draws n <;> simp [advance,hc,Nat.cast_add]
    simpa only [Nat.zero_add,IndependentStream.project_succ,MultiscaleActivation.count]
      using hstep.trans (add_le_add_right ih _)

/-- The source activation budget is discharged for the concrete virtual
counter, under private × iid Bernoulli × arbitrary independent frames. -/
theorem master_activation_sixteenth {I Private : Type} [MeasurableSpace I] [MeasurableSpace Private]
    (fx : I → Frame dx Kx) (fu : I → Frame du Ku) (initial : Private → S)
    (ν : Measure I) [IsProbabilityMeasure ν] (ρ : Measure Private) [IsProbabilityMeasure ρ]
    (p : ℝ) (hp : 0<p) (hp1 : p≤1) (N T : ℕ) (hT : 0<T)
    (hn : (N:ℝ)≤(T:ℝ)/(16*p)) :
    ((ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1))).prod ν).real
      {z | T≤(masterRun Px Pu A reply z.1.2 (fx z.2) (fu z.2) N 0 (initial z.1.1,0)).2}≤1/16 := by
  let stream := IndependentStream.law (BernoulliOracle.law p hp1)
  let μ := (ρ.prod stream).prod ν
  have hfst : MeasurePreserving Prod.fst μ (ρ.prod stream) :=
    ⟨measurable_fst,by simp only [μ,Measure.map_fst_prod,measure_univ,one_smul]⟩
  have hsnd : MeasurePreserving Prod.snd (ρ.prod stream) stream :=
    ⟨measurable_snd,by simp only [Measure.map_snd_prod,measure_univ,one_smul]⟩
  have hproj := (IndependentStream.project_preserves (BernoulliOracle.law p hp1) N).comp (hsnd.comp hfst)
  have hm : MeasurableSet {z : IndependentDraws.Draws Bool N | (T:ℝ)≤MultiscaleActivation.count N z} :=
    measurableSet_le measurable_const (MultiscaleActivation.count_measurable N)
  have he := hproj.measure_preimage hm.nullMeasurableSet
  have hsub : {z : (Private × (ℕ → Bool)) × I |
      T≤(masterRun Px Pu A reply z.1.2 (fx z.2) (fu z.2) N 0 (initial z.1.1,0)).2}⊆
      {z | (T:ℝ)≤MultiscaleActivation.count N (IndependentStream.project N z.1.2)} := by
    intro z hz
    exact (Nat.cast_le.mpr hz).trans (master_counter_le_draws Px Pu A reply _ _ _ _ _)
  apply (measureReal_mono hsub).trans
  change μ.real ((IndependentStream.project N ∘ Prod.snd ∘ Prod.fst) ⁻¹'
    {z | (T:ℝ)≤MultiscaleActivation.count N z})≤1/16
  rw [measureReal_def,he]
  exact MultiscaleActivation.revelation_sixteenth N T hT p hp hp1 hn

end Bilevel.PolishedLiteralActualObserver
