import Bilevel.TransportRoundPrefix
import Bilevel.TransportRoundPosterior
import Bilevel.TransportObserverGeometry

/-! The free initial source disclosure is an actual conditional observation.
Its blind energy is exactly zero; the initial known-space law is not assumed
to remain the unconditioned prior after revealing that vector. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Bilevel.TransportRound
open EuclideanGaussian TransportNetwork ProjectionGeometry TransportObserver
set_option maxHeartbeats 600000

def initialGenerators (n D : ℕ) (y : Space D) : Generators n D 1 := fun v _ => if v=0 then y else 0

theorem singleton_family_span {D : ℕ} (y : Space D) :
    TransportGeneratorStore.span (fun _ : Fin 1 => y) = Submodule.span ℝ {y} := by
  unfold TransportGeneratorStore.span
  rw [Set.range_const]

theorem initial_known (n D : ℕ) (y : Space D) :
    known (initialGenerators n D y) = TransportNetwork.insert (fun _ => ⊥) 0 y := by
  funext v
  by_cases hv : v=0
  · subst v
    change TransportGeneratorStore.span (fun _ : Fin 1 => if (0 : Vertex n)=0 then y else 0) = _
    simp only [ite_true,singleton_family_span,TransportNetwork.insert,Function.update_self,bot_sup_eq]
  · change TransportGeneratorStore.span (fun _ : Fin 1 => if v=0 then y else 0) = _
    simp only [if_neg hv,singleton_family_span,Submodule.span_zero_singleton,
      TransportNetwork.insert,Function.update_of_ne hv]

theorem seed_eq_initial {n D : ℕ} (T : ℕ) (hT : T≤D) (hpos : 0<T) (z : Latent n D) :
    seed T hT z = initialGenerators n D (frame T hT z 0 ⟨0,hpos⟩) := by
  funext v i
  simp only [seed,initialGenerators,dif_pos hpos]

theorem initial_posterior {n D : ℕ} (T : ℕ) (hT : T≤D) (hpos : 0<T) :
    ∀ᵐ y ∂(TransportNetwork.law n D).map (namedObservation T hT 0 ⟨0,hpos⟩),
      Invariant (known (initialGenerators n D y))
        (condDistrib id (namedObservation T hT 0 ⟨0,hpos⟩) (TransportNetwork.law n D) y) := by
  have hh := named_posterior_invariant T hT (fun _ : Vertex n => ⊥)
    (TransportNetwork.law n D) (law_invariant _) 0 ⟨0,hpos⟩
  simpa only [initial_known] using hh

theorem seed_blind_zero {n D : ℕ} (T : ℕ) (hT : T≤D) (hpos : 0<T)
    (z : Latent n D) (v : Vertex n) (I : Finset (Fin T)) (hI : ∀ i∈I, ¬Protected 0 v i) :
    frameEnergy (known (seed T hT z) v) (frame T hT z v) I=0 := by
  rw [seed_eq_initial T hT hpos z,initial_known]
  unfold frameEnergy
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hv : v=0
  · subst v
    have hine : (⟨0,hpos⟩ : Fin T)≠i := by
      intro he
      have hf := hI i hi
      apply hf
      rw [← he]
      simp [Protected]
    have ho := (frame_orthonormal T hT z (0 : Vertex n)).2 hine
    have hm : frame T hT z 0 i ∈ (Submodule.span ℝ {frame T hT z 0 ⟨0,hpos⟩})ᗮ :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mpr ho
    have hp := congrArg Subtype.val (Submodule.orthogonalProjection_eq_zero_iff.mpr hm)
    rw [TransportNetwork.insert,Function.update_self,bot_sup_eq]
    change ‖project (Submodule.span ℝ {frame T hT z 0 ⟨0,hpos⟩}) (frame T hT z 0 i)‖^2=0
    change project (Submodule.span ℝ {frame T hT z 0 ⟨0,hpos⟩}) (frame T hT z 0 i)=0 at hp
    rw [hp,norm_zero]
    norm_num
  · have hp : project (⊥ : Submodule ℝ (Space D)) (frame T hT z v i)=0 := by
      simpa using (project_mem (⊥ : Submodule ℝ (Space D)) (frame T hT z v i))
    simp only [TransportNetwork.insert,Function.update_of_ne hv,energy,hp,norm_zero,zero_pow (by decide : 2≠0)]

end Bilevel.TransportRound

