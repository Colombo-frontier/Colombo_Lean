import MatchingBounds1005.MainLower
import MatchingBounds1005.CUPGMainUpper
import MatchingBounds1005.MinimaxConversion

/-! Matching randomized first-order accuracy exponent, including the exact
distributional lower, deterministic upper and numerical minimax sandwich. -/
namespace MatchingBounds1005.Model

theorem main_theorem : MainTheorem :=
  mainTheorem_of_bounds main_lower_bound main_upper_bound

end MatchingBounds1005.Model
