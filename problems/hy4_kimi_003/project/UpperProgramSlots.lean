import UpperProgram

/-! Exact round/coordinate/parity identities for the actual paid query slots. -/

namespace Task006.Full

def upperSlot {d T : ℕ} (t : Fin T) (i : Fin d) (side : Fin 2) : Fin (upperReplyCount d T) :=
  ⟨2 * (t.val * d + i.val) + side.val, by
    have hm := Nat.mul_le_mul_right d (Nat.succ_le_of_lt t.isLt)
    unfold upperReplyCount
    nlinarith [i.isLt, side.isLt]⟩

theorem upperSlot_handle {d T : ℕ} (t : Fin T) (i : Fin d) (side : Fin 2) :
    (upperSlot t i side).val / 2 = t.val * d + i.val := by
  change (2 * (t.val * d + i.val) + side.val) / 2 = _
  rw [Nat.mul_add_div (by norm_num : 0 < 2), Nat.div_eq_of_lt side.isLt, Nat.add_zero]

theorem upperSlot_parity {d T : ℕ} (t : Fin T) (i : Fin d) (side : Fin 2) :
    (upperSlot t i side).val % 2 = side.val := by
  change (2 * (t.val * d + i.val) + side.val) % 2 = side.val
  simp [Nat.add_mod, Nat.mod_eq_of_lt side.isLt]

theorem upperRound_slot {d T : ℕ} (hd : 0 < d) (t : Fin T) (i : Fin d) (side : Fin 2) :
    upperRound hd (upperSlot t i side) = t := by
  apply Fin.ext
  change (2 * (t.val * d + i.val) + side.val) / (2 * d) = t.val
  have hid : 2 * (t.val * d + i.val) + side.val = (2 * d) * t.val + (2 * i.val + side.val) := by ring
  rw [hid, Nat.mul_add_div (by omega : 0 < 2 * d),
    Nat.div_eq_of_lt (by nlinarith [i.isLt, side.isLt] : 2 * i.val + side.val < 2 * d), Nat.add_zero]

theorem upperCoordinate_slot {d T : ℕ} (hd : 0 < d) (t : Fin T) (i : Fin d) (side : Fin 2) :
    upperCoordinate hd (upperSlot t i side) = i := by
  apply Fin.ext
  change ((upperSlot t i side).val / 2) % d = i.val
  rw [upperSlot_handle]
  simp [Nat.add_mod, Nat.mod_eq_of_lt i.isLt]

theorem upperQueryPoint_slot {d T : ℕ} (P : UpperProgramParameters) (hd : 0 < d)
    (t : Fin T) (i : Fin d) (side : Fin 2) (seed : UpperSeed d T)
    (h : Transcript (upperReplyCount d T)) :
    upperQueryPoint P hd (upperSlot t i side) seed h =
      upperIterate P seed h t.val + P.ρ • ((seed t).2 i).val +
        (if side.val = 0 then -P.δ else P.δ) • Task006.HaarRebalancing.column (seed t).1 i := by
  simp only [upperQueryPoint, upperRound_slot hd, upperCoordinate_slot hd, upperSlot_parity]

theorem upperSlot_before_round_end {d T : ℕ} (t : Fin T) (i : Fin d) (side : Fin 2) :
    (upperSlot t i side).val < 2 * d * (t.val + 1) := by
  change 2 * (t.val * d + i.val) + side.val < _
  nlinarith [i.isLt, side.isLt]

theorem upperSlot_before_later_round {d T : ℕ} (t : Fin T) (i : Fin d) (side : Fin 2)
    {s : ℕ} (hts : t.val < s) : (upperSlot t i side).val < 2 * d * s := by
  have hb := upperSlot_before_round_end t i side
  have hm := Nat.mul_le_mul_left (2 * d) (Nat.succ_le_of_lt hts)
  exact lt_of_lt_of_le hb hm

#print axioms upperQueryPoint_slot
#print axioms upperSlot_before_later_round

end Task006.Full
