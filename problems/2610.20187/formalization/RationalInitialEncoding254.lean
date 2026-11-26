import RationalRunEncoding254
import RationalMagnitude254

noncomputable section
open Matrix
namespace Paper254

theorem rationalHistoryInitial_height {d : ℕ} (w0 : Fin d→ℚ) (H : ℚ) (b : ℕ)
    (hH : RationalHeight H b) : MatrixHeight (rationalHistoryInitial w0 H).covariance b := by
  obtain ⟨Z,q,hq,hqb,hZ,hr⟩ := hH
  refine ⟨fun i j=>if i=j then Z 0 0 else 0,q,hq,hqb,?_,?_⟩
  · intro i j
    dsimp only
    split_ifs
    · exact hZ 0 0
    · simp
  · intro i j
    have hh : H=(Z 0 0:ℚ)/(q:ℚ) := hr 0 0
    by_cases hij : i=j
    · simp [rationalHistoryInitial,Matrix.smul_apply,hij,hh]
    · simp [rationalHistoryInitial,Matrix.smul_apply,hij]

theorem numberedBirthPrior_height (T K a : ℕ) (i : Fin (T+1))
    (hK : (K+1:ℤ)≤(2:ℤ)^a) :
    MatrixHeight (fun e (_ : Fin 1)=>numberedBirthPrior T K i e) a := by
  refine ⟨fun e _=>if ((numberedExpertEquiv T K).symm e).1=i then 1 else 0,
    (K+1:ℤ),by omega,?_,?_,?_⟩
  · simpa only [abs_of_nonneg (by positivity : (0:ℤ)≤K+1)] using hK
  · intro e _
    dsimp only
    split_ifs
    · simpa using (one_le_pow₀ (by norm_num : (1:ℤ)≤2) : (1:ℤ)≤2^a)
    · simp
  · intro e _
    unfold numberedBirthPrior
    dsimp only
    split_ifs <;> push_cast <;> simp

end Paper254
#print axioms Paper254.rationalHistoryInitial_height
#print axioms Paper254.numberedBirthPrior_height
