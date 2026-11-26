import RationalErrorEnvelope254

noncomputable section
namespace Paper254

private def PowerEnvelope (Q x : ℝ) (n : ℕ) : Prop := 0≤x ∧ x≤Q^n

private theorem PowerEnvelope.mul {Q x y : ℝ} {m n : ℕ}
    (hx : PowerEnvelope Q x m) (hy : PowerEnvelope Q y n) (hQ : 0≤Q) :
    PowerEnvelope Q (x*y) (m+n) := by
  constructor
  · exact mul_nonneg hx.1 hy.1
  · simpa [pow_add] using mul_le_mul hx.2 hy.2 hy.1 (pow_nonneg hQ m)

private theorem PowerEnvelope.add {Q x y : ℝ} {m n : ℕ}
    (hx : PowerEnvelope Q x m) (hy : PowerEnvelope Q y n) (hQ : 2≤Q) :
    PowerEnvelope Q (x+y) (m+n+1) := by
  have hQ1 : 1≤Q := by linarith
  have hx' := hx.2.trans (pow_le_pow_right₀ hQ1 (by omega : m≤m+n))
  have hy' := hy.2.trans (pow_le_pow_right₀ hQ1 (by omega : n≤m+n))
  constructor
  · exact add_nonneg hx.1 hy.1
  · rw [pow_succ]
    have hh := mul_le_mul_of_nonneg_left hQ (pow_nonneg (by linarith : 0≤Q) (m+n))
    linarith

private theorem PowerEnvelope.pow {Q x : ℝ} {m : ℕ} (hx : PowerEnvelope Q x m) (n : ℕ) :
    PowerEnvelope Q (x^n) (m*n) := by
  exact ⟨pow_nonneg hx.1 n,by simpa [pow_mul] using pow_le_pow_left₀ hx.1 hx.2 n⟩

private theorem PowerEnvelope.enlarge {Q x : ℝ} {m n : ℕ}
    (hx : PowerEnvelope Q x m) (hQ : 1≤Q) (hmn : m≤n) : PowerEnvelope Q x n :=
  ⟨hx.1,hx.2.trans (pow_le_pow_right₀ hQ hmn)⟩

theorem local_error_coefficients_polynomial (d : ℕ) (D lo hi G lam Q : ℝ)
    (hQ : 2≤Q) (hD : 0≤D) (hlo : 0<lo) (hhi : 0≤hi) (hG : 0≤G) (hlam : 0≤lam)
    (hdQ : (d:ℝ)≤Q) (hDQ : D≤Q) (hloQ : lo≤Q) (hlinvQ : lo⁻¹≤Q)
    (hhiQ : hi≤Q) (hGQ : G≤Q) (hlamQ : lam≤Q) :
    0≤localLinearCoefficient d D lo hi ∧ localLinearCoefficient d D lo hi≤Q^(5*d+60) ∧
    0≤localRootCoefficient d D lo ∧ localRootCoefficient d D lo≤Q^(5*d+60) ∧
    0≤meanErrorCoefficient d lo hi (uniformHistoryRadius d D hi G lam) ∧
      meanErrorCoefficient d lo hi (uniformHistoryRadius d D hi G lam)≤Q^(5*d+60) := by
  have hQ0 : 0≤Q := by linarith
  have hQ1 : 1≤Q := by linarith
  have pd : PowerEnvelope Q (d:ℝ) 1 := ⟨Nat.cast_nonneg _,by simpa using hdQ⟩
  have pD : PowerEnvelope Q D 1 := ⟨hD,by simpa using hDQ⟩
  have plo : PowerEnvelope Q lo 1 := ⟨hlo.le,by simpa using hloQ⟩
  have pli : PowerEnvelope Q lo⁻¹ 1 := ⟨by positivity,by simpa using hlinvQ⟩
  have phi : PowerEnvelope Q hi 1 := ⟨hhi,by simpa using hhiQ⟩
  have pG : PowerEnvelope Q G 1 := ⟨hG,by simpa using hGQ⟩
  have plam : PowerEnvelope Q lam 1 := ⟨hlam,by simpa using hlamQ⟩
  have p1 : PowerEnvelope Q 1 0 := by constructor <;> norm_num
  have p2 : PowerEnvelope Q 2 1 := ⟨by norm_num,by simpa using hQ⟩
  have p54 : PowerEnvelope Q (5/4) 1 := ⟨by norm_num,by simpa using (show (5/4:ℝ)≤Q by linarith)⟩
  have pR : PowerEnvelope Q (uniformHistoryRadius d D hi G lam) 10 := by
    exact ((pD.add ((((p54.mul plam hQ0).mul (pd.pow 3) hQ0).mul phi hQ0).mul pG hQ0) hQ).add p1 hQ)
  have pK : PowerEnvelope Q (precisionErrorCoefficient d lo) 14 := by
    simpa only [precisionErrorCoefficient,div_eq_mul_inv] using
      ((((pd.pow 3).mul pli hQ0).pow 2).mul pd hQ0).mul
        (p2.add (p2.mul (pd.pow 2) hQ0) hQ) hQ0
  have pM : PowerEnvelope Q (max 1 ((d:ℝ)^2/lo)) 3 := by
    have hh := (pd.pow 2).mul pli hQ0
    exact ⟨le_trans (by norm_num) (le_max_left _ _),max_le
      (one_le_pow₀ hQ1) (by simpa [div_eq_mul_inv] using hh.2)⟩
  have pC : PowerEnvelope Q (meanErrorCoefficient d lo hi (uniformHistoryRadius d D hi G lam)) 56 := by
    have h1 := (pK.add p1 hQ).mul (pR.pow 2) hQ0
    have h2 := (p2.mul (((pd.pow 2).mul pli hQ0).add p1 hQ) hQ0).mul pR hQ0
    have hh := phi.mul (p1.add ((p2.mul (pd.pow 2) hQ0).mul (h1.add h2 hQ) hQ0) hQ) hQ0
    simpa only [meanErrorCoefficient,div_eq_mul_inv] using hh
  have pperm : PowerEnvelope Q (Fintype.card (Equiv.Perm (Fin d)):ℝ) d := by
    constructor
    · positivity
    · have hp : (Fintype.card (Equiv.Perm (Fin d)):ℝ)≤(d:ℝ)^d := by
        rw [Fintype.card_perm,Fintype.card_fin]
        exact_mod_cast Nat.factorial_le_pow d
      exact hp.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hdQ d)
  have hdet := (((pperm.mul pd hQ0).mul (pM.pow d) hQ0).mul (phi.pow d) hQ0)
  have pA0 := (((plo.mul pd hQ0).add hdet hQ).add ((pd.pow 2).mul (pD.pow 2) hQ0) hQ).mul pK hQ0
  have pA : PowerEnvelope Q (localLinearCoefficient d D lo hi) (5*d+23) := by
    have hform : localLinearCoefficient d D lo hi =
      (lo*d+(Fintype.card (Equiv.Perm (Fin d)):ℝ)*d*(max 1 ((d:ℝ)^2/lo))^d*hi^d+
        (d:ℝ)^2*D^2)*precisionErrorCoefficient d lo/2 := by
      dsimp [localLinearCoefficient]
      simp only [one_div,inv_pow,div_inv_eq_mul]
    rw [hform]
    have he : 1+1+(d+1+3*d+1*d)+1+(1*2+1*2)+1+14=5*d+23 := by omega
    rw [he] at pA0
    exact ⟨div_nonneg pA0.1 (by norm_num),by linarith [pA0.1,pA0.2]⟩
  have pB : PowerEnvelope Q (localRootCoefficient d D lo) 6 :=
    ((pd.pow 2).mul pM hQ0).mul pD hQ0
  exact ⟨pA.1,(pA.enlarge hQ1 (by omega)).2,pB.1,(pB.enlarge hQ1 (by omega)).2,
    pC.1,(pC.enlarge hQ1 (by omega)).2⟩

theorem explicit_actual_history_precision (d a b s v : ℕ) (hv : 1≤v)
    (D G lam : ℝ) (lo hi : ℚ) (hD : 0≤D) (hG : 0≤G) (hlam : 0≤lam)
    (hlo : 0<(lo:ℝ)) (hhi : 0<(hi:ℝ))
    (hdv : (d:ℝ)≤(2:ℝ)^v) (hDv : D≤(2:ℝ)^v) (hlov : (lo:ℝ)≤(2:ℝ)^v)
    (hliv : (lo:ℝ)⁻¹≤(2:ℝ)^v) (hhiv : (hi:ℝ)≤(2:ℝ)^v)
    (hGv : G≤(2:ℝ)^v) (hlamv : lam≤(2:ℝ)^v) :
    let k := (5*d+60)*v
    let r := 2*s+4*k+4
    actualHistoryLocalError d D (lo:ℝ) (hi:ℝ) G lam
      (uniformHistoryParameters a b r r lo hi) (((2:ℝ)^(r+2))⁻¹)≤((2:ℝ)^s)⁻¹ := by
  have hQ : (2:ℝ)≤(2:ℝ)^v := by
    simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hv
  obtain ⟨hA,hAb,hB,hBb,hC,hCb⟩ := local_error_coefficients_polynomial d D (lo:ℝ) (hi:ℝ) G lam
    ((2:ℝ)^v) hQ hD hlo hhi.le hG hlam hdv hDv hlov hliv hhiv hGv hlamv
  let k := (5*d+60)*v
  have heq : ((2:ℝ)^v)^(5*d+60)=(2:ℝ)^k := by dsimp [k]; rw [←pow_mul,Nat.mul_comm v]
  rw [heq] at hAb hBb hCb
  have hC2 : meanErrorCoefficient d (lo:ℝ) (hi:ℝ) (uniformHistoryRadius d D (hi:ℝ) G lam)≤((2:ℝ)^k)^2 := by
    have hh : (1:ℝ)≤2^k := one_le_pow₀ (by norm_num)
    exact hCb.trans (by nlinarith)
  exact (actual_history_error_envelope d a b (2*s+4*k+4) D G lam lo hi hD hG hlam hlo hhi).trans
    (explicit_sqrt_error_budget _ _ _ k s hA hB hC hAb hBb hC2)

theorem explicit_history_precision_and_guards (d s v : ℕ) (hd : 0<d) (hv : 1≤v)
    (D G lam : ℝ) (lo hi : ℚ) (hD : 0≤D) (hG : 0≤G) (hlam : 0≤lam)
    (hlo : 0<(lo:ℝ)) (hgap : (lo:ℝ)<(hi:ℝ))
    (hdv : (d:ℝ)≤(2:ℝ)^v) (hDv : D≤(2:ℝ)^v) (hlov : (lo:ℝ)≤(2:ℝ)^v)
    (hliv : (lo:ℝ)⁻¹≤(2:ℝ)^v) (hhiv : (hi:ℝ)≤(2:ℝ)^v)
    (hGv : G≤(2:ℝ)^v) (hlamv : lam≤(2:ℝ)^v)
    (hgapv : ((hi:ℝ)-(lo:ℝ))⁻¹≤(2:ℝ)^v) :
    let r := 2*s+4*((5*d+60)*v)+4
    UniformHistoryGuards d (uniformHistoryParameters v v r r lo hi) (lo:ℝ) (hi:ℝ) ∧
      actualHistoryLocalError d D (lo:ℝ) (hi:ℝ) G lam
        (uniformHistoryParameters v v r r lo hi) (((2:ℝ)^(r+2))⁻¹)≤((2:ℝ)^s)⁻¹ := by
  let r := 2*s+4*((5*d+60)*v)+4
  have hrv : v≤r := by dsimp [r]; nlinarith
  have hsep : ((2:ℝ)^r)⁻¹≤(hi:ℝ)-(lo:ℝ) := by
    have hs := (inv_le_inv₀ (by positivity : (0:ℝ)<2^v)
      (inv_pos.mpr (sub_pos.mpr hgap))).mpr hgapv
    rw [inv_inv] at hs
    exact ((inv_le_inv₀ (by positivity) (by positivity)).mpr
      (pow_le_pow_right₀ (by norm_num) hrv)).trans hs
  exact ⟨uniformHistoryParameters_guards d v v r r hd hdv lo hi hlo hhiv hsep,
    explicit_actual_history_precision d v v s v hv D G lam lo hi hD hG hlam hlo
      (hlo.trans hgap) hdv hDv hlov hliv hhiv hGv hlamv⟩

end Paper254
#print axioms Paper254.explicit_actual_history_precision
#print axioms Paper254.explicit_history_precision_and_guards
