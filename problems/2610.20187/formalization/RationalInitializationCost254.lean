import IntegerMetadata254
import RationalMaterializedRun254

open scoped BigOperators
namespace Paper254

/-- The initial Gaussian is materialized once, then shared by live keys.
The two counters record scalar writes and integer coordinate tests. -/
def countedInitialGaussian {d : ℕ} (w0 : Fin d→ℚ) (hi : ℚ) :
    (RationalHistoryData d×ℕ)×ℕ :=
  let mean := Vector.ofFn w0
  let covariance := Vector.ofFn (fun i : Fin d => Vector.ofFn (fun j : Fin d => if i=j then hi else 0))
  ((⟨fun i=>mean.get i,fun i j=>(covariance.get i).get j⟩,d*d+d),d*d)

theorem countedInitialGaussian_value {d : ℕ} (w0 : Fin d→ℚ) (hi : ℚ) :
    (countedInitialGaussian w0 hi).1.1=rationalHistoryInitial w0 hi := by
  dsimp only [countedInitialGaussian,rationalHistoryInitial]
  congr 1
  · funext i
    simp [Vector.get]
  · ext i j
    by_cases h : i=j <;> simp [Vector.get,Matrix.one_apply,h]

/-- Initial live keys are generated and sorted once. The common birth
weight is divided once and cached; lists retain references to the shared
Gaussian, rather than allocating one copy per possible future birth. -/
def countedRationalInitialization {d : ℕ} (T K : ℕ) (w0 : Fin d→ℚ) (hi : ℚ) :
    (MaterializedRationalSparseData d ((T+1)*(K+1))×ℕ)×ℕ :=
  let live := fullyCountedStandardLive T K 0
  let gaussian := countedInitialGaussian w0 hi
  let mass : ℚ := 1/(K+1:ℚ)
  let histories := mapWithCosts (fun e=>((e,gaussian.1.1),1)) live.1
  let weights := mapWithCosts (fun e=>((e,mass),1)) live.1
  ((⟨histories.1,weights.1⟩,gaussian.1.2+1),
    live.2+gaussian.2+histories.2+weights.2+2)

theorem initial_live_prior (T K : ℕ) (e : Fin ((T+1)*(K+1)))
    (he : e∈(standardRationalSchedule T K).live 0) :
    numberedBirthPrior T K 0 e=1/(K+1:ℚ) := by
  have ha := (standardRationalSchedule_live (T := T) (K := K) (t := 0) (by omega)
    ((numberedExpertEquiv T K).symm e)).mp (by simpa using he)
  have hb : ((numberedExpertEquiv T K).symm e).1=0 := by
    apply Fin.ext
    change _=0
    have hbound := ha.2.1
    dsimp [expertBirth] at hbound
    omega
  simp [numberedBirthPrior,hb]

namespace RationalSparseConstruction
variable {d T K : ℕ} {D G eta : ℝ} {W : Domain d D}
variable (C : RationalSparseConstruction d T K D G eta W)

theorem initialization_program :
    (countedRationalInitialization T K C.initial_mean C.hi).1.1=C.materializedRun 1 0 0 0 := by
  simp only [countedRationalInitialization,fullyCountedStandardLive_program,
    mapWithCosts_values,countedInitialGaussian_value,materializedRun,
    MaterializedRationalSparseData.ofCompact]
  congr 1
  · apply List.map_congr_left
    intro e he
    have he' : e∈(standardRationalSchedule T K).live 0 := by simpa using he
    simp [CompactRationalSparseData.ambient,CompactRationalSparseData.restrict,initial,
      initialRationalSparse]
  · apply List.map_congr_left
    intro e he
    have he' : e∈(standardRationalSchedule T K).live 0 := by simpa using he
    simp [CompactRationalSparseData.weightView,CompactRationalSparseData.restrict,initial,
      initialRationalSparse,he',initial_live_prior T K e he']

end RationalSparseConstruction

def initializationMetadataBound (T K d : ℕ) : ℕ :=
  shortMetadataBound (Nat.log 2 (T+1)+1) K+3*Nat.log 2 (T+1)+4+
    d*d+2*standardLiveCap T K+2

theorem initialization_rational_charge {d : ℕ} (T K : ℕ) (w0 : Fin d→ℚ) (hi : ℚ) :
    (countedRationalInitialization T K w0 hi).1.2=d*d+d+1 := rfl

theorem initialization_metadata_charge {d : ℕ} (T K : ℕ) (w0 : Fin d→ℚ) (hi : ℚ) :
    (countedRationalInitialization T K w0 hi).2≤ initializationMetadataBound T K d := by
  have hlist : (fullyCountedStandardLive T K 0).1.length≤standardLiveCap T K := by
    rw [fullyCountedStandardLive_program,Finset.length_sort]
    exact standardRationalSchedule_uniform_card T K 0
  have hmeta := fullyCountedStandardLive_cost T K 0
  simp only [countedRationalInitialization,countedInitialGaussian,mapWithCosts_constant]
  dsimp only [initializationMetadataBound]
  omega

end Paper254
#print axioms Paper254.RationalSparseConstruction.initialization_program
#print axioms Paper254.initialization_metadata_charge
