import FreshGradientMinimax.LocalizedLower
import FreshGradientMinimax.LocalizedUpper

/-! The complete lower and upper assertions of Theorem 3.4. -/

set_option autoImplicit false
namespace FreshGradientMinimax

theorem theorem_34 : MainTheorem34Statement :=
  ⟨localized_lower_statement, localized_upper_statement⟩

end FreshGradientMinimax
