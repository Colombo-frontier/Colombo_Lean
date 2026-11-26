import SecondOrder.FiniteProductEntropy

open MeasureTheory InformationTheory
open scoped BigOperators Classical ENNReal

namespace SecondOrder
noncomputable section

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Relabel a finite probability law by a bijection. -/
def pmfTransport (e : α ≃ β) (p : PMF α) : PMF β :=
  PMF.ofFintype (fun b => p (e.symm b)) (by
    rw [Equiv.sum_comp e.symm]
    simpa only [tsum_fintype] using p.tsum_coe)

@[simp] theorem pmfTransport_apply (e : α ≃ β) (p : PMF α) (b : β) :
    pmfTransport e p b = p (e.symm b) := rfl

theorem pmfMean_transport (e : α ≃ β) (p : PMF α) (X : β → ℝ) :
    pmfMean (pmfTransport e p) X = pmfMean p (fun a => X (e a)) := by
  unfold pmfMean
  rw [← Equiv.sum_comp e (fun b => (pmfTransport e p b).toReal • X b)]
  simp

theorem pmfKL_transport (e : α ≃ β) (p q : PMF α) :
    pmfKL (pmfTransport e p) (pmfTransport e q) = pmfKL p q := by
  unfold pmfKL
  simp only [pmfTransport_apply]
  exact Equiv.sum_comp e.symm (fun a => (p a).toReal*Real.log ((p a).toReal/(q a).toReal))

theorem pmfTransport_eq_map (e : α ≃ β) (p : PMF α) : pmfTransport e p = p.map e := by
  ext b
  simp only [pmfTransport_apply, PMF.map_apply]
  rw [tsum_eq_single (e.symm b)]
  · simp
  · intro a ha
    have hb : b ≠ e a := by
      intro h
      apply ha
      simpa using (congrArg e.symm h).symm
    simp [hb]

theorem pmfTransport_uniform [Nonempty α] [Nonempty β] (e : α ≃ β) :
    pmfTransport e (PMF.uniformOfFintype α) = PMF.uniformOfFintype β := by
  ext b
  simp [pmfTransport_apply, PMF.uniformOfFintype_apply, Fintype.card_congr e]

end
end SecondOrder
