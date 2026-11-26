import RationalTaylorHeight254
import EfficientNewtonHeight254
import RationalTiltRadius254

noncomputable section
open Matrix
open scoped Matrix.Norms.Operator
namespace Paper254

theorem dyadic_matrix_height {m n : Type*} (A : Matrix m n ℚ) (p B : ℕ)
    (hrep : ∀ i j,∃ z : ℤ,A i j=(z:ℚ)/(2:ℚ)^p)
    (hmag : ∀ i j,|(A i j:ℝ)|≤(2:ℝ)^B) : MatrixHeight A (B+p) := by
  choose Z hZ using hrep
  refine ⟨Z,(2:ℤ)^p,pow_ne_zero _ (by norm_num),?_,?_,?_⟩
  · rw [abs_of_pos (by positivity : (0:ℤ)<2^p)]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  · intro i j
    have hh := hmag i j
    rw [hZ] at hh
    push_cast at hh
    rw [abs_div,abs_of_pos (by positivity : (0:ℝ)<2^p)] at hh
    have hb := (div_le_iff₀ (show (0:ℝ)<2^p by positivity)).mp hh
    rw [←pow_add] at hb
    exact_mod_cast hb
  · intro i j
    simpa using hZ i j

theorem dyadic_round_height {m n : Type*} (A : Matrix m n ℚ) (p B : ℕ)
    (hmag : ∀ i j,|(A i j:ℝ)|≤(2:ℝ)^B) :
    MatrixHeight (fun i j=>dyadicCeil p (A i j)) (B+1+p) := by
  apply dyadic_matrix_height _ p (B+1)
  · intro i j
    exact ⟨_,rfl⟩
  · intro i j
    have hh := dyadicCeil_real_bounds p (A i j)
    have ha := abs_le.mp (hmag i j)
    have hp : ((2:ℝ)^p)⁻¹≤1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    have hbase : (1:ℝ)≤2^B := one_le_pow₀ (by norm_num)
    rw [pow_succ]
    exact abs_le.mpr ⟨by linarith,by linarith⟩

def RationalMatrixBits {m n : Type*} (A : Matrix m n ℚ) (b : ℕ) : Prop :=
  ∀ i j,(A i j).num.natAbs.size≤b ∧ (A i j).den.size≤b

def RationalVectorBits {d : ℕ} (a : Fin d→ℚ) (b : ℕ) : Prop :=
  ∀ j,(a j).num.natAbs.size≤b ∧ (a j).den.size≤b

/-- The output-length clause of the manuscript's projection-oracle model.
The constants c and k describe its fixed polynomial, not an assumed history
invariant or regret conclusion. -/
def ProjectionEncodingSpec {d : ℕ} (oracle : RationalProjectionProcedure d)
    (L0 c k : ℕ) : Prop :=
  ∀ A a b p,(realMatrix A).PosDef→RationalMatrixBits A b→RationalVectorBits a b→
    RationalVectorBits (oracle A a p) (c*(d+L0+b+p+1)^k)

theorem rationalTiltMean_magnitude {d : ℕ} {D : ℝ} (W : Domain d D)
    (lo hi G : ℝ) (hhi : 0≤hi) (hG : 0≤G) (S : RationalHistoryData d)
    (hS : RationalHistoryInvariant W lo hi S) (lam : ℚ) (hlam : 0≤(lam:ℝ))
    (g w : Fin d→ℚ) (hg : ∀ i,|(g i:ℝ)|≤G)
    (hsmall : |2*(lam:ℝ)*((fun j=>(g j:ℝ)) ⬝ᵥ
      ((fun j=>(S.mean j:ℝ))-(fun j=>(w j:ℝ))))|≤1/4)
    (w0 : W.carrier) (v : ℕ) (hw0 : ∀ i,|w0.val i|≤(2:ℝ)^v)
    (hd : (d:ℝ)≤(2:ℝ)^v) (hD : D≤(2:ℝ)^v) (hH : hi≤(2:ℝ)^v)
    (hGb : G≤(2:ℝ)^v) (hlb : (lam:ℝ)≤(2:ℝ)^v) :
    ∀ i,|(rationalTiltMean S lam g w i:ℝ)|≤(2:ℝ)^(6*v+3) := by
  have hr := rationalTiltMean_uniform_radius W lo hi G hhi hG S hS lam hlam g w hg hsmall 0
  have hprod : (lam:ℝ)*(d:ℝ)^3*hi*G≤((2:ℝ)^v)^6 := by
    calc
      _ ≤ (2:ℝ)^v*((2:ℝ)^v)^3*(2:ℝ)^v*(2:ℝ)^v := by gcongr
      _ = _ := by ring
  have hK : (1:ℝ)≤2^v := one_le_pow₀ (by norm_num)
  have hK6 : (2:ℝ)^v≤((2:ℝ)^v)^6 := by
    calc
      _ = ((2:ℝ)^v)^1 := by simp
      _ ≤ _ := pow_le_pow_right₀ hK (by omega)
  have hexp : (2:ℝ)^(6*v+3)=8*((2:ℝ)^v)^6 := by
    rw [pow_add,pow_mul']
    norm_num
    ring
  intro i
  have hri := hr w0 i
  have ht := abs_sub_le (rationalTiltMean S lam g w i:ℝ) (w0.val i) 0
  rw [sub_zero,sub_zero,abs_sub_comm] at ht
  rw [hexp]
  have hw := hw0 i
  norm_num at hri
  nlinarith

/-- The three objects stored or supplied to projection have fixed dyadic
encoding bounds independent of earlier projection-output denominators. -/
theorem rationalHistoryStep_input_heights {d : ℕ} (hd : 0<d) {D : ℝ}
    (W : Domain d D) (oracle : RationalProjectionProcedure d) (hspec : RationalProjectionSpec W oracle)
    (cfg : RationalHistoryParameters) (lo hi G : ℝ) (hlo : 0<lo) (hhi : 0<hi) (hG : 0≤G)
    (guards : UniformHistoryGuards d cfg lo hi) (S : RationalHistoryData d)
    (hS : RationalHistoryInvariant W lo hi S) (lam : ℚ) (hlam : 0≤(lam:ℝ))
    (g w : Fin d→ℚ) (hg : ∀ i,|(g i:ℝ)|≤G)
    (hsmall : |2*(lam:ℝ)*((fun j=>(g j:ℝ)) ⬝ᵥ
      ((fun j=>(S.mean j:ℝ))-(fun j=>(w j:ℝ))))|≤1/4)
    (w0 : W.carrier) (v : ℕ) (hw0 : ∀ i,|w0.val i|≤(2:ℝ)^v)
    (hdim : (d:ℝ)≤(2:ℝ)^v) (hD : D≤(2:ℝ)^v) (hH : hi≤(2:ℝ)^v)
    (hLi : lo⁻¹≤(2:ℝ)^v) (hGb : G≤(2:ℝ)^v) (hlb : (lam:ℝ)≤(2:ℝ)^v) :
    MatrixHeight (rationalHistoryStep oracle cfg S lam g w).covariance (3*v+cfg.storagePrecision) ∧
    MatrixHeight (rationalProjectionMetric cfg S lam g) (3*v+1+cfg.storagePrecision) ∧
    MatrixHeight (fun i (_ : Fin 1)=>
      rationalVectorRound cfg.storagePrecision (rationalTiltMean S lam g w) i)
      (6*v+4+cfg.storagePrecision) := by
  have hn := rationalHistoryStep_preserves hd W oracle hspec cfg lo hi hlo hhi guards S hS lam g w
  let C := (rationalHistoryStep oracle cfg S lam g w).covariance
  have hpower : (d:ℝ)^2*hi≤(2:ℝ)^(3*v) := by
    calc
      _ ≤ ((2:ℝ)^v)^2*(2:ℝ)^v := by gcongr
      _ = _ := by rw [pow_mul']; ring
  have hipower : (d:ℝ)^2/lo≤(2:ℝ)^(3*v) := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ ((2:ℝ)^v)^2*(2:ℝ)^v := by gcongr
      _ = _ := by rw [pow_mul']; ring
  have hc : ∀ i j,|(C i j:ℝ)|≤(2:ℝ)^(3*v) := by
    intro i j
    exact (covariance_entry_bound (realMatrix C) hn.covariance_pos lo hi hhi.le
      hn.covariance_lower hn.covariance_upper i j).trans hpower
  have hprec := (precision_bounds_from_covariance (realMatrix C) hn.covariance_pos lo hi hlo hhi
    hn.covariance_lower hn.covariance_upper).2.2
  have hci : ∀ i j,|(rationalMatrixInverse C i j:ℝ)|≤(2:ℝ)^(3*v) := by
    intro i j
    have he := congrArg (fun M : Precision d=>M i j) (realMatrix_inverse C)
    rw [←Matrix.nonsing_inv_eq_ringInverse] at he
    change (rationalMatrixInverse C i j:ℝ)=(realMatrix C)⁻¹ i j at he
    rw [he]
    exact (hprec i j).trans hipower
  refine ⟨?_,?_,?_⟩
  · exact dyadic_matrix_height C cfg.storagePrecision (3*v)
      (rationalHistoryStep_covariance_encoding oracle cfg S lam g w) hc
  · exact dyadic_round_height (rationalMatrixInverse C) cfg.storagePrecision (3*v) hci
  · have ha := rationalTiltMean_magnitude W lo hi G hhi.le hG S hS lam hlam g w hg hsmall
      w0 v hw0 hdim hD hH hGb hlb
    exact dyadic_round_height (fun i (_ : Fin 1)=>rationalTiltMean S lam g w i)
      cfg.storagePrecision (6*v+3) (fun i _=>ha i)

theorem projection_mean_encoding_from_inputs {d : ℕ} (oracle : RationalProjectionProcedure d)
    (L0 c k : ℕ) (henc : ProjectionEncodingSpec oracle L0 c k)
    (cfg : RationalHistoryParameters) (S : RationalHistoryData d) (lam : ℚ)
    (g w : Fin d→ℚ) (b : ℕ)
    (hmetric : (realMatrix (rationalProjectionMetric cfg S lam g)).PosDef)
    (hB : RationalMatrixBits (rationalProjectionMetric cfg S lam g) b)
    (ha : RationalVectorBits (rationalVectorRound cfg.storagePrecision (rationalTiltMean S lam g w)) b) :
    RationalVectorBits (rationalHistoryStep oracle cfg S lam g w).mean
      (c*(d+L0+b+cfg.projectionPrecision+1)^k) :=
  henc _ _ b cfg.projectionPrecision hmetric hB ha

/-- End-to-end stored-state reset under precisely the projection output-size
interface in the paper. No bound on the previous mean's encoding is required. -/
theorem rationalHistoryStep_stored_bits {d : ℕ} (hd : 0<d) {D : ℝ}
    (W : Domain d D) (oracle : RationalProjectionProcedure d) (hspec : RationalProjectionSpec W oracle)
    (L0 c k : ℕ) (henc : ProjectionEncodingSpec oracle L0 c k)
    (cfg : RationalHistoryParameters) (lo hi G : ℝ) (hlo : 0<lo) (hhi : 0<hi) (hG : 0≤G)
    (guards : UniformHistoryGuards d cfg lo hi) (S : RationalHistoryData d)
    (hS : RationalHistoryInvariant W lo hi S) (lam : ℚ) (hlam : 0≤(lam:ℝ))
    (g w : Fin d→ℚ) (hg : ∀ i,|(g i:ℝ)|≤G)
    (hsmall : |2*(lam:ℝ)*((fun j=>(g j:ℝ)) ⬝ᵥ
      ((fun j=>(S.mean j:ℝ))-(fun j=>(w j:ℝ))))|≤1/4)
    (w0 : W.carrier) (v : ℕ) (hw0 : ∀ i,|w0.val i|≤(2:ℝ)^v)
    (hdim : (d:ℝ)≤(2:ℝ)^v) (hD : D≤(2:ℝ)^v) (hH : hi≤(2:ℝ)^v)
    (hLi : lo⁻¹≤(2:ℝ)^v) (hGb : G≤(2:ℝ)^v) (hlb : (lam:ℝ)≤(2:ℝ)^v) :
    MatrixHeight (rationalHistoryStep oracle cfg S lam g w).covariance (3*v+cfg.storagePrecision) ∧
    RationalVectorBits (rationalHistoryStep oracle cfg S lam g w).mean
      (c*(d+L0+(6*v+4+cfg.storagePrecision+1)+cfg.projectionPrecision+1)^k) := by
  have hh := rationalHistoryStep_input_heights hd W oracle hspec cfg lo hi G hlo hhi hG guards
    S hS lam hlam g w hg hsmall w0 v hw0 hdim hD hH hLi hGb hlb
  have hn := rationalHistoryStep_preserves hd W oracle hspec cfg lo hi hlo hhi guards S hS lam g w
  have hmetric : (realMatrix (rationalProjectionMetric cfg S lam g)).PosDef :=
    rationalMetricRound_posDef _ hn.covariance_pos lo hi hlo hhi
      hn.covariance_lower hn.covariance_upper cfg.storagePrecision guards.metric
  refine ⟨hh.1,?_⟩
  apply projection_mean_encoding_from_inputs oracle L0 c k henc cfg S lam g w
    (6*v+4+cfg.storagePrecision+1) hmetric
  · exact (hh.2.1.mono (by omega)).reduced_bits
  · intro j
    exact hh.2.2.reduced_bits j 0

end Paper254
#print axioms Paper254.projection_mean_encoding_from_inputs
#print axioms Paper254.rationalHistoryStep_stored_bits
