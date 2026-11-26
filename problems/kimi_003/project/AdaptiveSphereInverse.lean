import AdaptiveSphereFrameCore

open MeasureTheory
open scoped Matrix
namespace Task006.AdaptiveSphereFrame
open Task006.HaarRebalancing
noncomputable section
variable {d : ℕ}

theorem orthogonal_inverse_measurable :
    Measurable (fun B : OrthogonalGroup d => B⁻¹) := by
  exact (continuous_inv : Continuous (fun B : OrthogonalGroup d => B⁻¹)).measurable

#print axioms orthogonal_inverse_measurable

theorem orthogonal_action_measurable :
    Measurable (fun p : OrthogonalGroup d × E d => action p.1 p.2) :=
  (action_joint_continuous (d := d)).measurable

#print axioms orthogonal_action_measurable

theorem orthogonal_inverse_action_measurable :
    Measurable (fun p : OrthogonalGroup d × E d => action p.1⁻¹ p.2) := by
  have hf : Measurable (Prod.fst : OrthogonalGroup d × E d → OrthogonalGroup d) := measurable_fst
  have hi : Measurable (fun p : OrthogonalGroup d × E d => p.1⁻¹) :=
    (orthogonal_inverse_measurable (d := d)).comp hf
  have hp : Measurable (fun p : OrthogonalGroup d × E d => (p.1⁻¹,p.2)) :=
    hi.prodMk measurable_snd
  have hresult := (orthogonal_action_measurable (d := d)).comp hp
  simpa only [Function.comp_def] using hresult

#print axioms orthogonal_inverse_action_measurable

end
end Task006.AdaptiveSphereFrame
