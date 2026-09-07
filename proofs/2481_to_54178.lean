-- Equation2481 → Equation54178
-- Recorded verdict: false
-- Premise: x = (x ◇ ((y ◇ z) ◇ y)) ◇ y
-- Conclusion: x ◇ (y ◇ y) = x ◇ (y ◇ (z ◇ y))
-- Original submission SHA-256: 2fc56f819308bd1b5945c7f3e0005d9938035f911791ad5a98ff673c4bbf6c71
-- Aurora-accepted correction SHA-256: 41d7db0435e83152014c9dc8059bdaaf67ac2bd905c1c2e35f23efa0d167d50d
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ ((y ◇ z) ◇ y)) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ y) = x ◇ (y ◇ (z ◇ y))
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Aurora-accepted corrected submission body
                   

namespace submission

namespace CM2481_54178

inductive V where
  | zero
  | odd (n : Nat)
  | even (n : Nat)
  deriving DecidableEq

def color : V → Bool
  | .zero | .even _ => false
  | .odd _ => true

def step : V → Bool → V
  | .zero, false => .zero
  | .odd n, false => .even n
  | .even n, false => .odd n
  | .zero, true => .odd 0
  | .odd 0, true => .zero
  | .odd (n + 1), true => .even n
  | .even n, true => .odd (n + 1)

def op (x y : V) : V := step x (color y)

def instMagma : Magma V where
  op := op

theorem right_congr (a b c : V) (h : color b = color c) :
    op a b = op a c := by
  simp [op, h]

theorem involutive (a b : V) : op (op a b) b = a := by
  cases a with
  | zero => cases h : color b <;> simp [op, step, h]
  | odd n =>
      cases n with
      | zero => cases h : color b <;> simp [op, step, h]
      | succ n => cases h : color b <;> simp [op, step, h]
  | even n => cases h : color b <;> simp [op, step, h]

theorem right_color (a b : V) : color (op (op a b) a) = color a := by
  simp only [op]
  cases a with
  | zero => cases h : color b <;> rfl
  | odd n =>
      cases n with
      | zero => cases h : color b <;> rfl
      | succ n => cases h : color b <;> rfl
  | even n => cases h : color b <;> rfl

theorem source (x y z : V) :
    x = op (op x (op (op y z) y)) y := by
  rw [right_congr x (op (op y z) y) y (right_color y z)]
  exact (involutive x y).symm

theorem target_not :
    ¬ ∀ x y z : V,
      op x (op y y) = op x (op y (op z y)) := by
  intro h
  have bad := h .zero .zero (.even 0)
  exact (by decide :
    op .zero (op .zero .zero) ≠
      op .zero (op .zero (op (.even 0) .zero))) bad

end CM2481_54178

def certificate : Goal := by
  refine ⟨CM2481_54178.V, CM2481_54178.instMagma, ?_, ?_⟩
  · intro x y z
    exact CM2481_54178.source x y z
  · exact CM2481_54178.target_not

end submission

def submission : Goal := submission.certificate

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_2481_to_54178 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_2481_to_54178
