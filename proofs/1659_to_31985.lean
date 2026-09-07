-- Equation1659 → Equation31985
-- Recorded verdict: false
-- Premise: x = (x ◇ y) ◇ ((y ◇ y) ◇ z)
-- Conclusion: x = (x ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y
-- Original submission SHA-256: e5affb3d82f4274f8b25b690bcb95020839195ac942d3c821886760dac0b94be
-- Aurora-accepted correction SHA-256: 593c7bcc7f3912c92e83f02884294258f80a1f92fa0f1ceefaedefc4dd151303
-- Generator: equational-challenges standalone v2
-- All project definitions are embedded in this file.

-- Embedded module: JudgeMagma.Magma
section
/- Magma class, ◇ notation, and helpers for building finite magmas. -/

class Magma (α : Type _) where
  /-- The binary magma operation, written `◇`. -/
  op : α → α → α

@[inherit_doc] infix:65 " ◇ " => Magma.op

/-- Build a `Magma (Fin n)` from a flat list of values.
    Entry at index `i*n + j` gives the result of `i ◇ j`.
    Usage: `instance : Magma (Fin 3) := magmaFin 3 [0,0,0, 0,0,0, 0,0,1]`

    Marked `@[implicit_reducible]` because Lean 4.32 requires class-valued
    definitions to be transparent to instance resolution. Deliberately not
    plain `@[reducible]`: that would unfold the table literal during general
    unification too, which is pure cost for the large `Fin n` tables here. -/
@[implicit_reducible]
def magmaFin (n : Nat) (table : List Nat) : Magma (Fin n) where
  op a b :=
    let idx := a.val * n + b.val
    ⟨table[idx]! % n, Nat.mod_lt _ (Fin.pos a)⟩
end

-- Embedded module: JudgeProblem
section
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ y) ◇ ((y ◇ y) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (x ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Aurora-accepted corrected submission body
                   

namespace submission

namespace CM1659_31985

inductive R
  | zero
  | odd (n : Nat)
  | even (n : Nat)
  deriving DecidableEq

def parity : R → Bool
  | .zero => false
  | .odd _ => true
  | .even _ => false

def up : R → R
  | .zero => .odd 0
  | .odd n => .even n
  | .even n => .odd (n + 1)

def down : R → R
  | .zero => .zero
  | .odd 0 => .zero
  | .odd (n + 1) => .even n
  | .even n => .odd n

def op (x y : R) : R :=
  if parity x = parity y then up x else down x

theorem source (x y z : R) :
    x = op (op x y) (op (op y y) z) := by
  cases x with
  | zero =>
      cases y <;> cases z <;> simp [op, parity, up, down]
  | odd n =>
      cases n with
      | zero => cases y <;> cases z <;> simp [op, parity, up, down]
      | succ n => cases y <;> cases z <;> simp [op, parity, up, down]
  | even n =>
      cases y <;> cases z <;> simp [op, parity, up, down]

theorem target_not :
    ¬ ∀ x y : R, x = op (op x (op (op y (op y y)) y)) y := by
  intro h
  have bad := h .zero .zero
  exact R.noConfusion bad

end CM1659_31985

def certificate : Goal := by
  refine ⟨CM1659_31985.R, ⟨CM1659_31985.op⟩, ?_, ?_⟩
  · exact CM1659_31985.source
  · exact CM1659_31985.target_not

end submission

def submission : Goal := submission.certificate

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_1659_to_31985 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_1659_to_31985
