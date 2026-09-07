-- Equation1167 → Equation13465
-- Recorded verdict: false
-- Premise: x = y ◇ ((z ◇ (y ◇ y)) ◇ x)
-- Conclusion: x = x ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ x)
-- Original submission SHA-256: c4483ecf04a12f6f6b81086420f55d0bc10e9c63179a5f4ab6e4152564b84bc2
-- Aurora-accepted correction SHA-256: 29aaa8d3224d7b4d69e10b62cda47abb7fab935103ddf3988aeb546c7a203b86
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ ((z ◇ (y ◇ y)) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G), x = x ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ x)
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Aurora-accepted corrected submission body
                   

namespace submission

namespace CM1167_13465

inductive R
  | zero
  | odd (n : Nat)
  | even (n : Nat)
  deriving DecidableEq

def parity : R → Bool
  | .zero => false | .odd _ => true | .even _ => false

def up : R → R
  | .zero => .odd 0 | .odd n => .even n | .even n => .odd (n + 1)

def down : R → R
  | .zero => .zero
  | .odd 0 => .zero
  | .odd (n + 1) => .even n
  | .even n => .odd n

def f (x y : R) : R :=
  if parity x = parity y then up x else down x

def op (x y : R) : R := f y x

theorem source (x y z : R) :
    x = op y (op (op z (op y y)) x) := by
  cases x with
  | zero => cases y <;> cases z <;> simp [op, f, parity, up, down]
  | odd n =>
      cases n with
      | zero => cases y <;> cases z <;> simp [op, f, parity, up, down]
      | succ n => cases y <;> cases z <;> simp [op, f, parity, up, down]
  | even n => cases y <;> cases z <;> simp [op, f, parity, up, down]

theorem target_not :
    ¬ ∀ x : R, x = op x (op (op x (op (op x x) x)) x) := by
  intro h
  have bad := h .zero
  exact R.noConfusion bad

end CM1167_13465

end submission


def submission : Goal := by
  refine ⟨submission.CM1167_13465.R, ⟨submission.CM1167_13465.op⟩, ?_, ?_⟩
  · exact submission.CM1167_13465.source
  · exact submission.CM1167_13465.target_not

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_1167_to_13465 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_1167_to_13465
