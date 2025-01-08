namespace Test

theorem hyp {p : Prop} (h : p) : p := by exact h

theorem conjuction {p q : Prop} (hp : p) (hq : q) : p ∧ q := by exact ⟨hp, hq⟩

theorem foo (a : Nat) : a + 0 = 0 + a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.add_zero]
    rewrite [Nat.zero_add]
    rfl

theorem foo_inline_sequence (a : Nat) : a + 0 = 0 + a := by
  rw [Nat.add_zero]; rewrite [Nat.zero_add]; rfl

theorem parallel {P Q : Prop} (p : P) (q : Q) : P ∧ Q := by
  constructor <;> assumption

def function_on_nats (a b : Nat) : Nat := by
  exact a + b
