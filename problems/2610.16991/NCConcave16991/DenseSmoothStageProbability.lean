import NCConcave16991.DenseSmoothShortEvent
import NCConcave16991.DenseWeakStageBankLaw

/-! # Actual short completed stages have probability at most one eighth

Each section fixes every other static bank. The first entrance is then
selected from strict-past data, and its selected initialization row is the
only input from the current bank before the censored experiment starts.
-/

noncomputable section

namespace NCConcave16991.DenseSmooth.Revelation

open DenseWeakHiding

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

variable (n m T D : ℕ) (hn : 0 < n) (hD : 0 < D) (hm : m ≤ n)
  (hparity : m % 2 = n % 2) (hρ : 0 < (m : ℝ) / n)

theorem signTable_samePrefix_insert (j : Fin (T + 1)) (a b : ColumnBank n m D)
    (others : StageBank n m D T) :
    SamePrefix (CensoredSpace D) n T ((m : ℝ) / n) j
      (signTable hn hD hm hparity (Fin.insertNth (α := fun _ : Fin (T + 1) ↦ ColumnBank n m D) j a others))
      (signTable hn hD hm hparity (Fin.insertNth (α := fun _ : Fin (T + 1) ↦ ColumnBank n m D) j b others)) := by
  intro l hl
  have he : Fin.insertNth (α := fun _ : Fin (T + 1) ↦ ColumnBank n m D) j a others l = Fin.insertNth (α := fun _ : Fin (T + 1) ↦ ColumnBank n m D) j b others l := by
    rw [Fin.insertNth_apply_below hl,Fin.insertNth_apply_below hl]
  constructor
  · change normalizedSignVector (fun d ↦ hiddenSign ((Fin.insertNth (α := fun _ : Fin (T + 1) ↦ ColumnBank n m D) j a others) l d).1) =
      normalizedSignVector (fun d ↦ hiddenSign ((Fin.insertNth (α := fun _ : Fin (T + 1) ↦ ColumnBank n m D) j b others) l d).1)
    rw [he]
  · intro i
    change normalizedSignVector (fun d ↦ columnSign ((Fin.insertNth (α := fun _ : Fin (T + 1) ↦ ColumnBank n m D) j a others) l d).2.val i) =
      normalizedSignVector (fun d ↦ columnSign ((Fin.insertNth (α := fun _ : Fin (T + 1) ↦ ColumnBank n m D) j b others) l d).2.val i)
    rw [he]

variable {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy (Domain n T hn ((m : ℝ) / n) hρ) (n := n)
    (dx := primalDimension (CensoredSpace D) T) Ω)

def ShortCompletedEvent (seed : Ω) (N r : ℕ) (j : Fin T) : Set (StageBank n m D (T + 1)) :=
  {bank | j.val < frontier (CensoredSpace D) n T hn ((m : ℝ) / n) hρ
      (runWithTable (CensoredSpace D) n T hn ((m : ℝ) / n) hρ P seed (signTable hn hD hm hparity bank) N) ∧
    (runWithTable (CensoredSpace D) n T hn ((m : ℝ) / n) hρ P seed
      (signTable hn hD hm hparity bank) N).assigned j.castSucc < r}

theorem short_completed_section_probability_le (seed : Ω) (N r : ℕ) (j : Fin T)
    (hrn : r < n) (hbudget : 8 * m + 9 * r ≤ n)
    (hcoef : (32 / 63 : ℝ) * r * ((m : ℝ) / ((n : ℝ) - r)) ^ 2 ≤ 1 / 8000)
    (hDim : 512 * Real.log (((N + 2 : ℕ) : ℝ) + 2) + 2048 ≤ (D : ℝ))
    (others : StageBank n m D T) :
    (columnBankLaw n m D hm).eventMass {a |
      Fin.insertNth (α := fun _ : Fin (T + 1) ↦ ColumnBank n m D) j.castSucc a others ∈ ShortCompletedEvent n m T D hn hD hm hparity hρ P seed N r j} ≤ 1 / 8 := by
  let A (a : ColumnBank n m D) := signTable hn hD hm hparity (Fin.insertNth (α := fun _ : Fin (T + 1) ↦ ColumnBank n m D) j.castSucc a others)
  let B := A (others j)
  have hpref (a : ColumnBank n m D) : SamePrefix (CensoredSpace D) n T ((m : ℝ) / n) j.castSucc (A a) B :=
    signTable_samePrefix_insert n m T D hn hD hm hparity j.castSucc a (others j) others
  have hrow (a : ColumnBank n m D) (i : Fin n) :
      normalizedReply (fun d ↦ columnBit (a d) i) = (A a).row i j.castSucc := by
    rw [normalizedReply_row]
    change normalizedSignVector (fun d ↦ columnSign (a d).2.val i) =
      normalizedSignVector (fun d ↦ columnSign ((Fin.insertNth (α := fun _ : Fin (T + 1) ↦ ColumnBank n m D) j.castSucc a others) j.castSucc d).2.val i)
    rw [Fin.insertNth_apply_same]
  have hdir (a : ColumnBank n m D) : (A a).direction j.castSucc =
      normalizedSignVector (fun d ↦ hiddenSign (bankLabels a d)) := by
    change normalizedSignVector (fun d ↦ hiddenSign ((Fin.insertNth (α := fun _ : Fin (T + 1) ↦ ColumnBank n m D) j.castSucc a others) j.castSucc d).1) = _
    rw [Fin.insertNth_apply_same]
    rfl
  have hDim' : 512 * Real.log (((N + 1 + 1 : ℕ) : ℝ) + 2) + 2048 ≤ (D : ℝ) := by
    simpa only [Nat.add_assoc,show 1 + 1 = 2 from rfl] using hDim
  by_cases hj : j.val = 0
  · let s₀ := initial (CensoredSpace D) n T hn ((m : ℝ) / n) hρ
    have hfront : frontier (CensoredSpace D) n T hn ((m : ℝ) / n) hρ s₀ = j.val := by
      simpa only [s₀,initial,frontier,Machine.initial,Counter.initial] using hj.symm
    have hseen : s₀.base.progress.2 = ∅ := rfl
    have hbound := censored_empty_alignment_probability_le n T D hn ((m : ℝ) / n) hρ P hm hparity seed s₀ hseen
      (N + 1) r hrn hbudget hcoef
      (fun s d ↦ queryProbe (CensoredSpace D) n T hn ((m : ℝ) / n) hρ P seed j.castSucc s d)
      (fun s ↦ queryProbe_sum_squares n T hn ((m : ℝ) / n) hρ D P seed j.castSucc s) hDim'
    apply (FiniteLaw.eventMass_mono (columnBankLaw n m D hm) ?_).trans hbound
    intro a ha
    obtain ⟨hcomplete,hshort⟩ := ha
    exact short_completion_empty_event n T D hn ((m : ℝ) / n) hρ P hD seed (A a) j N 0 r s₀ hfront
      (fun i d ↦ columnBit (a d) i) (hrow a) rfl (bankLabels a) (hdir a) hcomplete hshort
  · by_cases henter : j.val ≤ frontier (CensoredSpace D) n T hn ((m : ℝ) / n) hρ
        (runWithTable (CensoredSpace D) n T hn ((m : ℝ) / n) hρ P seed B N)
    · obtain ⟨t,ht,hfirst⟩ := exists_firstEntry (CensoredSpace D) n T hn ((m : ℝ) / n) hρ P seed B j.castSucc
        (by change 0 < j.val; omega) N henter
      obtain ⟨hf,o,ho,hc⟩ := firstEntry_details (CensoredSpace D) n T hn ((m : ℝ) / n) hρ P seed B j.castSucc t hfirst
      let s := runWithTable (CensoredSpace D) n T hn ((m : ℝ) / n) hρ P seed B t
      let start := entryStart (CensoredSpace D) n T hn ((m : ℝ) / n) hρ s o
        (B.row o.1 (stageIndex (CensoredSpace D) n T hn ((m : ℝ) / n) hρ s))
        (B.direction (stageIndex (CensoredSpace D) n T hn ((m : ℝ) / n) hρ s))
        (fun i ↦ B.row i (stageIndex (CensoredSpace D) n T hn ((m : ℝ) / n) hρ s))
      have hv : frontier (CensoredSpace D) n T hn ((m : ℝ) / n) hρ s < T + 1 := hfirst.1.trans j.castSucc.isLt
      have hvnext : frontier (CensoredSpace D) n T hn ((m : ℝ) / n) hρ s + 1 < T + 1 := by
        rw [hf]
        exact j.castSucc.isLt
      have hstartFront (a : CensoredSpace D) : frontier (CensoredSpace D) n T hn ((m : ℝ) / n) hρ (start a) = j.val := by
        exact (entryStart_frontier (CensoredSpace D) n T hn ((m : ℝ) / n) hρ s o _ _ _ a hv).trans hf
      have hstartSeen (a : CensoredSpace D) : (start a).base.progress.2 = {o.1} :=
        entryStart_seen (CensoredSpace D) n T hn ((m : ℝ) / n) hρ s o _ _ _ hvnext a
      have hentry (a : ColumnBank n m D) :
          runWithTable (CensoredSpace D) n T hn ((m : ℝ) / n) hρ P seed (A a) (t + 1) =
            start (normalizedReply (fun d ↦ columnBit (a d) o.1)) := by
        obtain ⟨o',ho',hf',he'⟩ := firstEntry_eq_initialization (CensoredSpace D) n T hn ((m : ℝ) / n) hρ P seed
          (A a) B j.castSucc (hpref a) t hfirst
        have heo : o' = o := Sum.inr.inj (ho'.symm.trans ho)
        subst o'
        rw [hrow a o.1]
        exact he'
      have hbound := censored_alignment_probability_le n T D hn ((m : ℝ) / n) hρ P hm hparity seed o.1 start hstartSeen
        (N + 1) r hrn hbudget hcoef
        (fun s d ↦ queryProbe (CensoredSpace D) n T hn ((m : ℝ) / n) hρ P seed j.castSucc s d)
        (fun s ↦ queryProbe_sum_squares n T hn ((m : ℝ) / n) hρ D P seed j.castSucc s) hDim'
      apply (FiniteLaw.eventMass_mono (columnBankLaw n m D hm) ?_).trans hbound
      intro a ha
      obtain ⟨hcomplete,hshort⟩ := ha
      exact short_completion_initialized_event n T D hn ((m : ℝ) / n) hρ P hD seed (A a) j N (t + 1) r o.1 start
        hstartFront (fun i d ↦ columnBit (a d) i) (hrow a) (hentry a) (bankLabels a) (hdir a) hcomplete hshort
    · have hempty : {a | Fin.insertNth (α := fun _ : Fin (T + 1) ↦ ColumnBank n m D) j.castSucc a others ∈ ShortCompletedEvent n m T D hn hD hm hparity hρ P seed N r j} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro a ha
        have hh := (reached_iff_of_prefix (CensoredSpace D) n T hn ((m : ℝ) / n) hρ P seed (A a) B j.castSucc (hpref a) N).mp ha.1.le
        exact henter hh
      rw [hempty]
      simp [FiniteLaw.eventMass]

theorem short_completed_probability_le (seed : Ω) (N r : ℕ) (j : Fin T)
    (hrn : r < n) (hbudget : 8 * m + 9 * r ≤ n)
    (hcoef : (32 / 63 : ℝ) * r * ((m : ℝ) / ((n : ℝ) - r)) ^ 2 ≤ 1 / 8000)
    (hDim : 512 * Real.log (((N + 2 : ℕ) : ℝ) + 2) + 2048 ≤ (D : ℝ)) :
    (stageBankLaw n m D (T + 1) hm).eventMass
      (ShortCompletedEvent n m T D hn hD hm hparity hρ P seed N r j) ≤ 1 / 8 := by
  exact stageBank_coordinate_event_bound hm j.castSucc _ _
    (short_completed_section_probability_le n m T D hn hD hm hparity hρ P seed N r j hrn hbudget hcoef hDim)

end NCConcave16991.DenseSmooth.Revelation
