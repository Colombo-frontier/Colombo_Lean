import Bilevel.PolishedHistoryStationaryRun

/-! Joint one-step marginals of the actual Ionescu-Tulcea execution. These
retain the preceding prefix, rather than replacing it by a one-time marginal. -/
noncomputable section
open MeasureTheory ProbabilityTheory Preorder
namespace Bilevel.PolishedHistory
open HistoryProgram
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {S Q O Y H : Type*} [MeasurableSpace S] [MeasurableSpace Q]
  [MeasurableSpace O] [MeasurableSpace Y] [MeasurableSpace H]
variable (A : BorelAdaptive.Program S Q O Y) (R : HistoryProgram.Oracle Q O H)

def extendPrefix (n : ℕ) (z : Π _ : Finset.Iic n,S × H) (x : S × H) :
    Π _ : Finset.Iic (n+1),S × H :=
  IicProdIoc (X:=fun _ => S × H) n (n+1)
    (z,MeasurableEquiv.piSingleton (X:=fun _ => S × H) n x)

theorem extendPrefix_measurable (n : ℕ) (z : Π _ : Finset.Iic n,S × H) :
    Measurable (extendPrefix n z) :=
  measurable_IicProdIoc.comp (measurable_const.prodMk
    (MeasurableEquiv.piSingleton (X:=fun _ => S × H) n).measurable)

theorem extendPrefix_previous (n : ℕ) (z : Π _ : Finset.Iic n,S × H) (x : S × H) :
    extendPrefix n z x ⟨n,Finset.mem_Iic.mpr (Nat.le_succ n)⟩=last n z := by
  simp [extendPrefix,last,IicProdIoc_def]

theorem extendPrefix_next (n : ℕ) (z : Π _ : Finset.Iic n,S × H) (x : S × H) :
    last (n+1) (extendPrefix n z x)=x := by
  simp [extendPrefix,last,IicProdIoc_def,MeasurableEquiv.piSingleton]

/-- Exact joint prefix extension law: the next state is drawn from the
actual absorbing program transition at the last retained state. -/
theorem partial_one_step_law (n : ℕ) (z : Π _ : Finset.Iic n,S × H) :
    Kernel.partialTraj (X:=fun _ => S × H) (nextKernel A R) n (n+1) z=
      (HistoryProgram.step A R (last n z)).map (extendPrefix n z) := by
  let e := MeasurableEquiv.piSingleton (X:=fun _ => S × H) n
  let g : (Π _ : Finset.Ioc n (n+1),S × H) →
      (Π _ : Finset.Iic (n+1),S × H) :=
    fun x => IicProdIoc (X:=fun _ => S × H) n (n+1) (z,x)
  have hg : Measurable g := measurable_IicProdIoc.comp
    (measurable_const.prodMk measurable_id)
  have hI : Measurable (IicProdIoc (X:=fun _ => S × H) n (n+1)) :=
    measurable_IicProdIoc
  rw [Kernel.partialTraj_succ_self,Kernel.map_apply _ hI,
    Kernel.prod_apply,Kernel.id_apply,Measure.dirac_prod]
  have hmk : Measurable (Prod.mk z : (Π _ : Finset.Ioc n (n+1),S × H) →
      (Π _ : Finset.Iic n,S × H) × (Π _ : Finset.Ioc n (n+1),S × H)) :=
    measurable_const.prodMk measurable_id
  rw [Measure.map_map hI hmk]
  change ((nextKernel A R n).map e z).map g=_
  rw [Kernel.map_apply _ e.measurable,Measure.map_map hg e.measurable]
  rfl

def prefixStepGood (v : S → ℝ) (n : ℕ) (w : Π _ : Finset.Iic (n+1),S × H) : Prop :=
  let z := w ⟨n,Finset.mem_Iic.mpr (Nat.le_succ n)⟩
  let z' := last (n+1) w
  A.halt z.1=true → A.halt z'.1=true ∧ v z'.1=v z.1

theorem prefixStepGood_measurable (v : S → ℝ) (hv : Measurable v) (n : ℕ) :
    MeasurableSet {w : (Π _ : Finset.Iic (n+1),S × H) | prefixStepGood A v n w} := by
  have hprev : Measurable (fun w : (Π _ : Finset.Iic (n+1),S × H) =>
      (w ⟨n,Finset.mem_Iic.mpr (Nat.le_succ n)⟩).1) :=
    measurable_fst.comp (measurable_pi_apply _)
  have hnext : Measurable (fun w : (Π _ : Finset.Iic (n+1),S × H) =>
      (last (n+1) w).1) := measurable_fst.comp (last_measurable (n+1))
  change MeasurableSet {w | A.halt ((w ⟨n,Finset.mem_Iic.mpr (Nat.le_succ n)⟩).1)=true →
    A.halt (last (n+1) w).1=true ∧ v (last (n+1) w).1=
      v (w ⟨n,Finset.mem_Iic.mpr (Nat.le_succ n)⟩).1}
  simp only [imp_iff_not_or]
  exact ((A.halt_measurable.comp hprev) (measurableSet_singleton true)).compl.union
    (((A.halt_measurable.comp hnext) (measurableSet_singleton true)).inter
      (measurableSet_eq_fun (hv.comp hnext) (hv.comp hprev)))

theorem partial_one_step_good (v : S → ℝ) (hv : Measurable v) (n : ℕ)
    (z : Π _ : Finset.Iic n,S × H) :
    ∀ᵐ w ∂Kernel.partialTraj (X:=fun _ => S × H) (nextKernel A R) n (n+1) z,
      prefixStepGood A v n w := by
  rw [partial_one_step_law]
  have hm := prefixStepGood_measurable (H:=H) A v hv n
  apply (ae_map_iff (extendPrefix_measurable n z).aemeasurable hm).mpr
  by_cases hh : A.halt (last n z).1=true
  · rw [HistoryProgram.step_halted _ _ _ hh]
    apply (ae_dirac_iff ((extendPrefix_measurable n z) hm)).mpr
    simp [prefixStepGood,extendPrefix_previous,extendPrefix_next,hh]
  · exact Filter.Eventually.of_forall (fun x => by
      simp [prefixStepGood,extendPrefix_previous,extendPrefix_next,hh])

def pathStepGood (v : S → ℝ) (n : ℕ) (w : HistoryProgram.Path S H) : Prop :=
  A.halt (w n).1=true → A.halt (w (n+1)).1=true ∧ v (w (n+1)).1=v (w n).1

theorem pathStepGood_measurable (v : S → ℝ) (hv : Measurable v) (n : ℕ) :
    MeasurableSet {w : HistoryProgram.Path S H | pathStepGood A v n w} := by
  have h := (measurable_frestrictLe (X:=fun _ => S × H) (n+1))
    (prefixStepGood_measurable (H:=H) A v hv n)
  simpa only [Set.preimage_setOf_eq,prefixStepGood,pathStepGood,last,frestrictLe_apply] using h

/-- The actual complete path law preserves the halt and every measurable
real observable after halting; no measurable diagonal on the algorithm
state space is required. -/
theorem trajectory_step_good (v : S → ℝ) (hv : Measurable v) (n : ℕ)
    (z₀ : Π _ : Finset.Iic 0,S × H) :
    ∀ᵐ w ∂HistoryProgram.trajectory A R z₀,pathStepGood A v n w := by
  let κ := nextKernel A R
  have hinner (z : Π _ : Finset.Iic n,S × H) :
      ∀ᵐ w ∂Kernel.traj (X:=fun _ => S × H) κ n z,pathStepGood A v n w := by
    have hp := partial_one_step_good A R v hv n z
    have he : (Kernel.traj (X:=fun _ => S × H) κ n z).map (frestrictLe (n+1))=
        Kernel.partialTraj (X:=fun _ => S × H) κ n (n+1) z :=
      Kernel.traj_map_frestrictLe_apply (X:=fun _ => S × H) (κ:=κ) n (n+1) z
    rw [← he] at hp
    have hh := (ae_map_iff (measurable_frestrictLe (X:=fun _ => S × H) (n+1)).aemeasurable
      (prefixStepGood_measurable (H:=H) A v hv n)).mp hp
    simpa only [prefixStepGood,pathStepGood,last,frestrictLe_apply] using hh
  change ∀ᵐ w ∂Kernel.traj (X:=fun _ => S × H) κ 0 z₀,pathStepGood A v n w
  have hc : Kernel.traj (X:=fun _ => S × H) κ n ∘ₖ
      Kernel.partialTraj (X:=fun _ => S × H) κ 0 n=Kernel.traj (X:=fun _ => S × H) κ 0 :=
    Kernel.traj_comp_partialTraj (X:=fun _ => S × H) (κ:=κ) (Nat.zero_le n)
  rw [← hc]
  exact (Kernel.ae_comp_iff (pathStepGood_measurable A v hv n)).mpr
    (Filter.Eventually.of_forall hinner)

theorem trajectoryLaw_step_good {Private : Type*} [MeasurableSpace Private]
    (privateLaw : Measure Private) (start : Private → S) (h₀ : H)
    (v : S → ℝ) (hv : Measurable v) (n : ℕ) :
    ∀ᵐ w ∂HistoryProgram.trajectoryLaw A R privateLaw start h₀,
      pathStepGood A v n w := by
  rw [HistoryProgram.trajectoryLaw,Measure.comp_eq_comp_const_apply]
  exact (Kernel.ae_comp_iff (pathStepGood_measurable A v hv n)).mpr
    (Filter.Eventually.of_forall (fun z => trajectory_step_good A R v hv n z))

end Bilevel.PolishedHistory
