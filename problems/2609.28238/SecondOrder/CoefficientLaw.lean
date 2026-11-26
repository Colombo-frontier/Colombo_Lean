import SecondOrder.BiasedSignLaw

open MeasureTheory InformationTheory
open scoped BigOperators Classical ENNReal

namespace SecondOrder
noncomputable section

/-- The original real-valued coefficient support {-R,R}. -/
def SignedCoefficient (R : ℝ) := ↥({-R,R} : Set ℝ)

instance signedCoefficient_fintype (R : ℝ) : Fintype (SignedCoefficient R) := by
  unfold SignedCoefficient
  infer_instance

instance signedCoefficient_measurable (R : ℝ) : MeasurableSpace (SignedCoefficient R) :=
  inferInstanceAs (MeasurableSpace ↥({-R,R} : Set ℝ))

instance signedCoefficient_singletons (R : ℝ) : MeasurableSingletonClass (SignedCoefficient R) :=
  inferInstanceAs (MeasurableSingletonClass ↥({-R,R} : Set ℝ))

instance signedCoefficient_nonempty (R : ℝ) : Nonempty (SignedCoefficient R) :=
  ⟨⟨R, by simp⟩⟩

def coefficientEquiv {R : ℝ} (hR : 0 < R) : Bool ≃ SignedCoefficient R where
  toFun b := ⟨R*signValue b, by cases b <;> simp [signValue]⟩
  invFun z := if z.1 = R then true else false
  left_inv b := by
    have hne : -R ≠ R := by linarith
    cases b <;> simp [signValue, hne]
  right_inv z := by
    apply Subtype.ext
    rcases z.property with h | h
    · have h' : z.1 ≠ R := by rw [h]; linarith
      simp only [if_neg h', signValue, mul_neg, mul_one]
      simpa using h.symm
    · simp only [Set.mem_singleton_iff] at h
      simp [h, signValue]

@[simp] theorem coefficientEquiv_value {R : ℝ} (hR : 0 < R) (b : Bool) :
    (coefficientEquiv hR b).1 = R*signValue b := rfl

def coefficientPMF (R c : ℝ) (hR : 2 ≤ R) (hc : c^2 = 1) : PMF (SignedCoefficient R) :=
  pmfTransport (coefficientEquiv (by linarith)) (biasedSignPMF R c hR hc)

def fairCoefficientPMF (R : ℝ) (hR : 2 ≤ R) : PMF (SignedCoefficient R) :=
  pmfTransport (coefficientEquiv (by linarith)) (PMF.uniformOfFintype Bool)

theorem fairCoefficientPMF_eq_uniform (R : ℝ) (hR : 2 ≤ R) :
    fairCoefficientPMF R hR = PMF.uniformOfFintype (SignedCoefficient R) :=
  pmfTransport_uniform _

theorem coefficientPMF_ne_zero (R c : ℝ) (hR : 2 ≤ R) (hc : c^2 = 1)
    (z : SignedCoefficient R) : coefficientPMF R c hR hc z ≠ 0 :=
  biasedSignPMF_ne_zero R c hR hc _

theorem fairCoefficientPMF_ne_zero (R : ℝ) (hR : 2 ≤ R) (z : SignedCoefficient R) :
    fairCoefficientPMF R hR z ≠ 0 := uniformBool_ne_zero _

theorem coefficientPMF_mean (R c : ℝ) (hR : 2 ≤ R) (hc : c^2 = 1) :
    (∫ z, z.1 ∂(coefficientPMF R c hR hc).toMeasure) = c := by
  rw [PMF.integral_eq_sum]
  change pmfMean (coefficientPMF R c hR hc) Subtype.val = c
  rw [coefficientPMF, pmfMean_transport]
  exact biasedSignPMF_mean R c hR hc

theorem fairCoefficientPMF_mean (R : ℝ) (hR : 2 ≤ R) :
    (∫ z, z.1 ∂(fairCoefficientPMF R hR).toMeasure) = 0 := by
  rw [PMF.integral_eq_sum]
  change pmfMean (fairCoefficientPMF R hR) Subtype.val = 0
  rw [fairCoefficientPMF, pmfMean_transport]
  change uniformMean (fun b => R*signValue b) = 0
  rw [uniformMean_bool]
  simp [signValue]

theorem pmfKL_coefficient (R c : ℝ) (hR : 2 ≤ R) (hc : c^2 = 1) :
    pmfKL (coefficientPMF R c hR hc) (fairCoefficientPMF R hR) = signKL (c/R) := by
  rw [coefficientPMF, fairCoefficientPMF, pmfKL_transport, pmfKL_biasedSign]

theorem klDiv_coefficient (R c : ℝ) (hR : 2 ≤ R) (hc : c^2 = 1) :
    klDiv (coefficientPMF R c hR hc).toMeasure (fairCoefficientPMF R hR).toMeasure ≤
      ENNReal.ofReal (1/R^2) := by
  rw [klDiv_pmf _ _ (fairCoefficientPMF_ne_zero R hR), pmfKL_coefficient]
  exact ENNReal.ofReal_le_ofReal (biased_sign_entropy hR hc)

/-- The manuscript's independent coefficient-array KL bound, on the actual
real-valued support, for any finite feature index set. -/
theorem klDiv_coefficientProduct {ι : Type*} [Fintype ι]
    (R : ℝ) (c : ι → ℝ) (hR : 2 ≤ R) (hc : ∀ i, c i^2 = 1) :
    klDiv (finitePiPMF (fun i => coefficientPMF R (c i) hR (hc i))).toMeasure
      (finitePiPMF (fun _ : ι => fairCoefficientPMF R hR)).toMeasure ≤
      ENNReal.ofReal ((Fintype.card ι:ℝ)/R^2) := by
  rw [klDiv_finitePi _ _ (fun i => coefficientPMF_ne_zero R (c i) hR (hc i))
    (fun _ => fairCoefficientPMF_ne_zero R hR)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∑ _i : ι, 1/R^2 := Finset.sum_le_sum (fun i _ => by
      rw [pmfKL_coefficient]
      exact biased_sign_entropy hR (hc i))
    _ = _ := by simp [div_eq_mul_inv]

theorem coefficientProduct_coordinate_mean {ι : Type*} [Fintype ι]
    (R : ℝ) (c : ι → ℝ) (hR : 2 ≤ R) (hc : ∀ i, c i^2 = 1) (i : ι) :
    (∫ z, (z i).1 ∂(finitePiPMF (fun j => coefficientPMF R (c j) hR (hc j))).toMeasure) =
      c i := by
  rw [PMF.integral_eq_sum]
  change pmfMean (finitePiPMF (fun j => coefficientPMF R (c j) hR (hc j)))
    (fun z : ι → SignedCoefficient R => (z i).1) = c i
  rw [finitePiPMF_coordinate_mean]
  simpa only [PMF.integral_eq_sum, pmfMean] using coefficientPMF_mean R (c i) hR (hc i)

end
end SecondOrder
