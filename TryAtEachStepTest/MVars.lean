namespace Test

-- We want to make sure that the presence of mvars in hypothesis types
-- does not confuse tryAtEachStep.

example (x y z : Nat) : x + y + z = z + y + x := by
  let h : True → ?_:= ?_
  · exact h True.intro
  intro _
  rw [Nat.add_comm x, Nat.add_assoc y, Nat.add_comm x,
      ←Nat.add_assoc, Nat.add_comm y]
