import NCConcave16991

/-! These assignments check the full closed types, including implicit arguments.
The Specification definitions encode the mathematical assumptions and quantifiers;
no external lower-bound or algorithm-correctness premise is supplied here. -/
example : NCConcave16991.Theorem31GlobalSpecification :=
  @NCConcave16991.theorem31_global
example : NCConcave16991.Theorem31PiecewiseSpecification :=
  @NCConcave16991.theorem31_piecewise
example : NCConcave16991.Theorem32Specification :=
  @NCConcave16991.theorem32_two_upper_bounds
example : NCConcave16991.Theorem33Specification :=
  @NCConcave16991.theorem33_two_lower_bounds
example : NCConcave16991.NormalizedBranchLowerSpecification :=
  @NCConcave16991.normalized_branch_randomized_lower

#print axioms NCConcave16991.theorem31_global
#print axioms NCConcave16991.theorem31_piecewise
#print axioms NCConcave16991.theorem32_two_upper_bounds
#print axioms NCConcave16991.theorem33_two_lower_bounds
#print axioms NCConcave16991.normalized_branch_randomized_lower
