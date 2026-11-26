import RationalSparseConstruction254
import RationalEncodingReset254
import RationalMasterEncoding254
import StandardRationalPrefix254

noncomputable section
namespace Paper254

theorem RationalMatrixBits.mono {m n : Type*} {A : Matrix m n ℚ} {b c : ℕ}
    (h : RationalMatrixBits A b) (hbc : b≤c) : RationalMatrixBits A c :=
  fun i j=>⟨(h i j).1.trans hbc,(h i j).2.trans hbc⟩

theorem RationalVectorBits.mono {d : ℕ} {a : Fin d→ℚ} {b c : ℕ}
    (h : RationalVectorBits a b) (hbc : b≤c) : RationalVectorBits a c :=
  fun j=>⟨(h j).1.trans hbc,(h j).2.trans hbc⟩

namespace RationalSparseConstruction
variable {d T K : ℕ} {D G eta : ℝ} {W : Domain d D}
variable (C : RationalSparseConstruction d T K D G eta W)

theorem update_history_bits (L0 c k v p q : ℕ)
    (henc : ProjectionEncodingSpec C.oracle L0 c k)
    (hp : ∀ j,(C.cfg j).storagePrecision≤p) (hq : ∀ j,(C.cfg j).projectionPrecision≤q)
    (hw0 : ∀ i,|(C.initial_mean i:ℝ)|≤(2:ℝ)^v)
    (hdim : (d:ℝ)≤(2:ℝ)^v) (hD : D≤(2:ℝ)^v) (hH : (C.hi:ℝ)≤(2:ℝ)^v)
    (hLi : ∀ j,(C.lo j:ℝ)⁻¹≤(2:ℝ)^v) (hGb : G≤(2:ℝ)^v) (hlb : (C.lam:ℝ)≤(2:ℝ)^v)
    (t : ℕ) (e : Fin ((T+1)*(K+1))) :
    let S := rationalHistoryStep C.oracle (C.allCfg e) ((C.run t).histories e)
      C.lam (C.gradient t) (C.prediction t)
    RationalMatrixBits S.covariance (3*v+p+1) ∧
      RationalVectorBits S.mean (c*(d+L0+6*v+p+q+6)^k) := by
  let j := ((numberedExpertEquiv T K).symm e).2
  have hs := (C.invariant t).histories e
  have hg : ∀ i,|(C.gradient t i:ℝ)|≤G := by
    intro i
    simpa only [Real.norm_eq_abs] using
      (PiLp.norm_apply_le (WithLp.toLp 2 (fun j=>(C.gradient t j:ℝ))) i).trans (C.gradient_bound t)
  have hsmall : |2*(C.lam:ℝ)*((fun i=>(C.gradient t i:ℝ)) ⬝ᵥ
      ((fun i=>(((C.run t).histories e).mean i:ℝ))-(fun i=>(C.prediction t i:ℝ))))|≤1/4 := by
    rw [C.lam_eq]
    exact coordinate_curvature_bound W C.diameter_pos C.gradient_pos C.curvature_pos _
      (C.gradient_bound t) ⟨_,hs.feasible⟩ ⟨_,C.prediction_feasible t⟩
  have hb := rationalHistoryStep_stored_bits C.dimension_pos W C.oracle C.oracle_spec L0 c k henc
    (C.allCfg e) (C.allLo e) (C.hi:ℝ) G (C.lo_pos j) C.hi_pos C.gradient_pos.le
    (C.guards j) ((C.run t).histories e) hs C.lam C.lam_pos.le (C.gradient t) (C.prediction t)
    hg hsmall ⟨WithLp.toLp 2 (fun i=>(C.initial_mean i:ℝ)),C.initial_feasible⟩ v hw0
    hdim hD hH (hLi j) hGb hlb
  dsimp only at hb ⊢
  constructor
  · apply RationalMatrixBits.mono hb.1.reduced_bits
    change 3*v+(C.cfg j).storagePrecision+1≤3*v+p+1
    have h₁ := hp j
    omega
  · apply RationalVectorBits.mono hb.2
    apply Nat.mul_le_mul_left c
    apply Nat.pow_le_pow_left
    change d+L0+(6*v+4+(C.cfg j).storagePrecision+1)+(C.cfg j).projectionPrecision+1≤_
    have h₁ := hp j
    have h₂ := hq j
    omega

/-- The storage bound holds at every actual state, including dormant and
expired histories. It does not recurse on the previous denominator size. -/
theorem run_history_bits (L0 c k v p q B0 : ℕ)
    (henc : ProjectionEncodingSpec C.oracle L0 c k)
    (hp : ∀ j,(C.cfg j).storagePrecision≤p) (hq : ∀ j,(C.cfg j).projectionPrecision≤q)
    (hw0 : ∀ i,|(C.initial_mean i:ℝ)|≤(2:ℝ)^v)
    (hdim : (d:ℝ)≤(2:ℝ)^v) (hD : D≤(2:ℝ)^v) (hH : (C.hi:ℝ)≤(2:ℝ)^v)
    (hLi : ∀ j,(C.lo j:ℝ)⁻¹≤(2:ℝ)^v) (hGb : G≤(2:ℝ)^v) (hlb : (C.lam:ℝ)≤(2:ℝ)^v)
    (hinitCov : RationalMatrixBits (rationalHistoryInitial C.initial_mean C.hi).covariance B0)
    (hinitMean : RationalVectorBits C.initial_mean B0) :
    ∀ t e,RationalMatrixBits ((C.run t).histories e).covariance (max B0 (3*v+p+1)) ∧
      RationalVectorBits ((C.run t).histories e).mean (max B0 (c*(d+L0+6*v+p+q+6)^k)) := by
  intro t
  induction t with
  | zero =>
    intro e
    exact ⟨hinitCov.mono (le_max_left _ _),hinitMean.mono (le_max_left _ _)⟩
  | succ t ih =>
    intro e
    have hs := C.update_history_bits L0 c k v p q henc hp hq hw0 hdim hD hH hLi hGb hlb t e
    have he : (C.run (t+1)).histories e=if e∈(standardRationalSchedule T K).live t then
        rationalHistoryStep C.oracle (C.allCfg e) ((C.run t).histories e)
          C.lam (C.gradient t) (C.prediction t) else (C.run t).histories e := rfl
    rw [he]
    split_ifs
    · exact ⟨hs.1.mono (le_max_right _ _),hs.2.mono (le_max_right _ _)⟩
    · exact ih e

theorem run_weight_bits (a : ℕ) (hcap : (standardLiveCap T K:ℤ)≤(2:ℤ)^a)
    (t : ℕ) (e : Fin ((T+1)*(K+1))) :
    ((C.run (t+1)).weights e).num.natAbs.size≤a+C.master_precision+4 ∧
    ((C.run (t+1)).weights e).den.size≤a+C.master_precision+4 := by
  let sch := standardRationalSchedule T K
  have hs := C.invariant t
  have hcard : ((sch.live (t+1)).card:ℤ)≤(2:ℤ)^a :=
    (Int.ofNat_le.mpr (standardRationalSchedule_uniform_card T K (t+1))).trans hcap
  have hz := rationalSparseExponents_bound W C.diameter_pos C.gradient_pos C.curvature_pos
    C.allLo (C.hi:ℝ) (sch.live t) (C.run t) hs C.lam C.lam_eq (C.gradient t) (C.gradient_bound t)
  have hsch := standardRationalSchedule_spec T K
  exact rationalMasterUpdate_reduced_bits C.master_precision a (sch.live t) (sch.live (t+1)) hcard
    (C.run t).weights (rationalSparseExponents C.lam (C.run t) (C.gradient t)) (sch.prior t) (sch.share t)
    hs.nonneg hs.total hs.support hz (hsch.prior_nonneg t) (hsch.prior_total t)
    (hsch.share_pos t) (hsch.share_le_one t) (hsch.prior_support t) e

end RationalSparseConstruction
end Paper254
#print axioms Paper254.RationalSparseConstruction.run_history_bits
#print axioms Paper254.RationalSparseConstruction.run_weight_bits
