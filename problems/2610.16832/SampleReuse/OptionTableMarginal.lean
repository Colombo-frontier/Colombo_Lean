import SampleReuse.PersistentOptionTable

open SecondOrder
open scoped Classical ENNReal BigOperators

namespace SampleReuse
noncomputable section

variable {Handle A : Type} [Fintype Handle] [Fintype A]

/-- Integrating out a nuisance dummy key leaves the immutable sample table
on the real handles with exactly its original product law. -/
theorem option_table_marginal_mean (q : PMF A) (p : Handle → PMF A) (F : (Handle → A) → ℝ) :
    pmfMean (finitePiPMF (fun key : Option Handle => key.elim q p))
      (fun table => F (fun r => table (some r))) = pmfMean (finitePiPMF p) F := by
  calc
    _ = pmfMean q (fun _ => pmfMean (finitePiPMF p) F) := by
      unfold pmfMean
      rw [← Equiv.sum_comp (Equiv.piOptionEquivProd (β := fun _ : Option Handle => A)).symm]
      simp only [finitePiPMF_apply,Fintype.prod_option,ENNReal.toReal_mul,
        Fintype.sum_prod_type,Equiv.piOptionEquivProd,Equiv.coe_fn_symm_mk,
        Option.elim_none,Option.elim_some,smul_eq_mul,Finset.mul_sum,mul_assoc]
    _ = _ := pmfMean_const q _

theorem option_table_marginal (q : PMF A) (p : Handle → PMF A) :
    (finitePiPMF (fun key : Option Handle => key.elim q p)).map
      (fun table => fun r => table (some r)) = finitePiPMF p := by
  ext table
  apply (ENNReal.toReal_eq_toReal (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [finite_pmf_map_toReal]
  have hh := option_table_marginal_mean q p (fun b => if b = table then (1:ℝ) else 0)
  simpa [pmfMean,smul_eq_mul] using hh

end
end SampleReuse
