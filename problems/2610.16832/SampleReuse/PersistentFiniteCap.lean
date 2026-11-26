import SampleReuse.PersistentStoppingPadding

open SecondOrder
namespace SampleReuse
noncomputable section

def finiteCapOutput {Q H Y O S Z : Type} (P : PersistentStoppingAlgorithm Q H Y O S)
    (reply : Q → Z → Y) (N : ℕ) (table : Fin (N+1) → Z) : O :=
  (normalizePersistentAlgorithm N P.cap).output N
    (persistentQueryRun (normalizePersistentAlgorithm N P.cap).toQueryPolicy reply table N)

def extendFiniteTable {Z : Type} (N : ℕ) (table : Fin (N+1) → Z) (n : ℕ) : Z :=
  table ⟨min n N,by omega⟩

theorem extendFiniteTable_apply {Z : Type} (N : ℕ) (table : Fin (N+1) → Z) (i : Fin (N+1)) :
    extendFiniteTable N table i.val = table i := by
  unfold extendFiniteTable
  congr 1
  apply Fin.ext
  exact min_eq_left (by omega)

theorem finiteCapOutput_as_lazy {Q H Y O S Z : Type} (P : PersistentStoppingAlgorithm Q H Y O S)
    (reply : Q → Z → Y) (N : ℕ) (table : Fin (N+1) → Z) :
    finiteCapOutput P reply N table = P.cap.output N
      (lazyPersistentRun P.cap.toQueryPolicy reply (extendFiniteTable N table) N).1 :=
  normalizePersistentAlgorithm_output N P.cap reply table (extendFiniteTable N table)
    (extendFiniteTable_apply N table)

theorem projectStopping_finiteCapOutput {H S Z : Type} {m d : ℕ} (U : Point m →ₗᵢ[ℝ] Point d)
    (P : PersistentStoppingAlgorithm (Point d) H (RichReply d) (Point d) S)
    (F : Z → Point m → ℝ) (hF : ∀ z, ContDiff ℝ 2 (F z)) (N : ℕ) (table : Fin (N+1) → Z) :
    finiteCapOutput (projectStoppingAlgorithm U P) (fun x z => richReply F z x) N table =
      isometryProjection U (finiteCapOutput P (fun x z => richReply (fun z => paddedLoss U (F z)) z x) N table) := by
  rw [finiteCapOutput_as_lazy,finiteCapOutput_as_lazy,projectStopping_cap_output U P F hF]

end
end SampleReuse
