import Bilevel.TransportAugmentedReplay

/-! The common auxiliary observer inserts ALL retained auxiliary columns
before the supplied current query vectors. This includes the shared known
space, while leaving the actual controller run and call count unchanged. -/
noncomputable section
open MeasureTheory
universe u v
namespace Bilevel.TransportAugmented
open EuclideanGaussian TransportNetwork TransportRound
set_option autoImplicit false
variable {C : Type u} {S : Type v} [MeasurableSpace C] [MeasurableSpace S]
  {n D p Tnet k T B : ℕ}

def retainedQueries (s : CommonState C S k T D) : Fin (k*(T+1)) → Space D :=
  fun a => (s.2.2 a.divNat).2 a.modNat

theorem retainedQueries_measurable (a : Fin (k*(T+1))) :
    Measurable (fun s : CommonState C S k T D => retainedQueries s a) :=
  (measurable_pi_apply a.modNat).comp (measurable_snd.comp
    ((measurable_pi_apply a.divNat).comp (measurable_snd.comp measurable_snd)))

def enlargeBatch (A : Controller C S n D p Tnet k T B) :
    Controller C S n D p Tnet k T (k*(T+1)+B) where
  choose := A.choose
  choose_measurable := A.choose_measurable
  auxiliaryQueries t s := Fin.addCases (retainedQueries s.1) (A.auxiliaryQueries t s)
  auxiliaryQueries_measurable t a := by
    refine Fin.addCases ?_ ?_ a
    · intro j
      simpa only [Fin.addCases_left] using
        (retainedQueries_measurable (C:=C) (S:=S) (D:=D) j).comp measurable_fst
    · intro j
      simpa only [Fin.addCases_right] using A.auxiliaryQueries_measurable t j
  respond := A.respond
  respond_measurable := A.respond_measurable
  networkOutput := A.networkOutput
  networkOutput_measurable := A.networkOutput_measurable
  auxiliaryOutput := A.auxiliaryOutput
  auxiliaryOutput_measurable := A.auxiliaryOutput_measurable

theorem enlargeBatch_run_eq (P : TransportAuxiliaryFrame.Schedule k T)
    (A : Controller C S n D p Tnet k T B) (hTnet : Tnet ≤ D)
    (names : ℕ → Vertex n → Fin 1 → Option (Fin Tnet))
    (s : NetworkMemory C S k T D × Generators n D 1) (z : Latent n D) (N : ℕ) :
    networkRun P (enlargeBatch A) hTnet names s z N=networkRun P A hTnet names s z N := rfl

theorem retained_mem_enlarged (A : Controller C S n D p Tnet k T B) (t : ℕ)
    (s : CommonState C S k T D × Generators n D (size n p 1 1 t)) (i : Fin k) (j : Fin (T+1)) :
    (s.1.2.2 i).2 j ∈ Set.range ((enlargeBatch A).auxiliaryQueries t s) := by
  refine ⟨Fin.castAdd B (finProdFinEquiv (i,j)),?_⟩
  simp only [enlargeBatch,Fin.addCases_left,retainedQueries]
  exact congrArg (fun a : Fin k × Fin (T+1) => (s.1.2.2 a.1).2 a.2)
    (finProdFinEquiv.symm_apply_apply (i,j))

theorem query_mem_enlarged (A : Controller C S n D p Tnet k T B) (t : ℕ)
    (s : CommonState C S k T D × Generators n D (size n p 1 1 t)) (b : Fin B) :
    A.auxiliaryQueries t s b ∈ Set.range ((enlargeBatch A).auxiliaryQueries t s) := by
  refine ⟨Fin.natAdd (k*(T+1)) b,?_⟩
  simp only [enlargeBatch,Fin.addCases_right]

def withAuxiliaryOutput (A : Controller C S n D p Tnet k T B)
    (output : CommonState C S k T D → Space D) (ho : Measurable output) :
    Controller C S n D p Tnet k T B :=
  {A with auxiliaryOutput := output, auxiliaryOutput_measurable := ho}

theorem withAuxiliaryOutput_run_eq (P : TransportAuxiliaryFrame.Schedule k T)
    (A : Controller C S n D p Tnet k T B) (hTnet : Tnet ≤ D)
    (names : ℕ → Vertex n → Fin 1 → Option (Fin Tnet))
    (output : CommonState C S k T D → Space D) (ho : Measurable output)
    (s : NetworkMemory C S k T D × Generators n D 1) (z : Latent n D) (N : ℕ) :
    networkRun P (withAuxiliaryOutput A output ho) hTnet names s z N=networkRun P A hTnet names s z N := rfl

end Bilevel.TransportAugmented
