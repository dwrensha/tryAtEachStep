namespace Test

theorem foo (a : Nat) : a + 0 = 0 + a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.add_zero]
    rewrite [Nat.zero_add]
    rfl
