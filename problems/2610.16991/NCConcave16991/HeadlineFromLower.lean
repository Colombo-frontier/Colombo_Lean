import NCConcave16991.UpperTheorem
import NCConcave16991.HeadlineReduction

/-! # Combining the proved upper bounds with the complementary lower theorem -/

namespace NCConcave16991

theorem theorem31Global_of_theorem33 (hlower : Theorem33Specification) : Theorem31GlobalSpecification :=
  theorem31Global_of_theorem32_and_theorem33 theorem32_two_upper_bounds hlower

theorem theorem31Piecewise_of_theorem33 (hlower : Theorem33Specification) : Theorem31PiecewiseSpecification :=
  theorem31Piecewise_of_theorem32_and_theorem33 theorem32_two_upper_bounds hlower

end NCConcave16991
