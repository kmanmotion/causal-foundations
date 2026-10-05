/- EXPECTED COMPILATION FAILURE. Excluded from all library imports/targets.
   The verification runner requires this false assertion to be rejected. -/
import Init
theorem deliberately_false : (2 : Nat) = 3 := by
  rfl
