import AdaptiveSphereResidualFrame

open MeasureTheory Set
open scoped Matrix

namespace Task006.AdaptiveSphereResidualFrame

open Task006.HaarRebalancing Task006.AdaptiveSphereBlock
noncomputable section
variable {d : ℕ}

theorem castOrthogonal_continuous {m n : ℕ} (h : m = n) :
    Continuous (castOrthogonal h) := by
  cases h
  exact continuous_id

/-- Joint continuity of the exact old-to-new stabilizer embedding. -/
theorem embedNext_joint_continuous (r : Fin d) :
    Continuous (fun p : OrthogonalGroup (d-r.val) × OrthogonalGroup (d-(r.val+1)) =>
      embedNext r p.1 p.2) := by
  have hdim : d-(r.val+1) = (d-r.val)-1 := by omega
  have hcast : Continuous (fun g : OrthogonalGroup (d-(r.val+1)) =>
      castOrthogonal hdim g) := castOrthogonal_continuous hdim
  have hblock : Continuous (fun g : OrthogonalGroup (d-(r.val+1)) =>
      blockOrthogonal (d-r.val) 1 (by omega) (castOrthogonal hdim g)) :=
    (blockOrthogonal_continuous (d-r.val) 1 (by omega)).comp hcast
  have hfirst : Continuous
      (Prod.fst : OrthogonalGroup (d-r.val) × OrthogonalGroup (d-(r.val+1)) →
        OrthogonalGroup (d-r.val)) := continuous_fst
  have hsecond := hblock.comp
    (continuous_snd : Continuous
      (Prod.snd : OrthogonalGroup (d-r.val) × OrthogonalGroup (d-(r.val+1)) →
        OrthogonalGroup (d-(r.val+1))))
  have hresult := (hfirst.mul hsecond).mul hfirst.inv
  change Continuous (fun p : OrthogonalGroup (d-r.val) × OrthogonalGroup (d-(r.val+1)) =>
    p.1 * blockOrthogonal (d-r.val) 1 (by omega) (castOrthogonal hdim p.2) * p.1⁻¹) at hresult
  simpa only [embedNext] using hresult

theorem embedNext_joint_measurable (r : Fin d) :
    Measurable (fun p : OrthogonalGroup (d-r.val) × OrthogonalGroup (d-(r.val+1)) =>
      embedNext r p.1 p.2) := (embedNext_joint_continuous r).measurable

theorem embedNext_control_continuous (r : Fin d) (H : OrthogonalGroup (d-r.val)) :
    Continuous (fun g : OrthogonalGroup (d-(r.val+1)) => embedNext r H g) := by
  have hresult := (embedNext_joint_continuous r).comp
    (continuous_const.prodMk continuous_id : Continuous
      (fun g : OrthogonalGroup (d-(r.val+1)) => (H,g)))
  simpa only [Function.comp_def] using hresult

/-- The old history may supply an arbitrary measurable Householder rotation. -/
theorem embedNext_past_measurable {H : Type*} [MeasurableSpace H]
    (r : Fin d) (rotation : H → OrthogonalGroup (d-r.val)) (hrotation : Measurable rotation) :
    Measurable (fun p : OrthogonalGroup (d-(r.val+1)) × H =>
      embedNext r (rotation p.2) p.1) := by
  have hresult := (embedNext_joint_measurable r).comp
    ((hrotation.comp measurable_snd).prodMk measurable_fst)
  simpa only [Function.comp_def] using hresult

#print axioms embedNext_joint_continuous
#print axioms embedNext_joint_measurable
#print axioms embedNext_control_continuous
#print axioms embedNext_past_measurable
end
end Task006.AdaptiveSphereResidualFrame
