import Paper254

/-!
MANDATORY MAIN-THEOREM ACCEPTANCE CHECK.
This check requires
proof terms of the complete statistical targets, with no additional
Gaussian, restart, minimax, or regret assumptions.

Simply compiling definitions of Prop does not satisfy this check.
Do not replace these examples with implication theorems, extra assumptions,
axioms, or admitted terms. On success, inspect the axioms below as well.
-/

example : Paper254.MainCurvedStatement := Paper254.main_curved
example : Paper254.MainUpperStatement := Paper254.main_upper
example : Paper254.ClippedUpperStatement := Paper254.main_clipped_upper
example : Paper254.MainLowerStatement := Paper254.main_lower
example : Paper254.DimensionOptimalStatement := Paper254.dimension_optimal

#print axioms Paper254.main_curved
#print axioms Paper254.main_upper
#print axioms Paper254.main_clipped_upper
#print axioms Paper254.main_lower
#print axioms Paper254.dimension_optimal
