namespace Test

example (x y : Nat) : x + y = y + 0 + x := by
  conv => rhs
          lhs
          rw [Nat.add_zero]
  exact Nat.add_comm _ _
