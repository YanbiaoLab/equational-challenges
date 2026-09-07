-- Equation14746 → Equation24393
-- Recorded verdict: false
-- Premise: x = y ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ x)
-- Conclusion: x = ((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ x)
-- Original submission SHA-256: 11760e5eb0124d66706a98a3b9e5ea07045f5ae5a0ecad755d2b88c21256f89c
-- Aurora-accepted correction SHA-256: 76ab63c1fe47aff3abb2c618d7cc0d42868d4d9f5da4c721c1bc4600a979b09f
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = ((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ x)
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Aurora-accepted corrected submission body
                   

namespace submission

namespace CM14746_24393

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
def f (x y : R) : R := if parity x = parity y then up x else down x
def op (x y : R) : R := f y x

theorem source (x y : R) :
    x = op y (op (op (op y y) (op y y)) x) := by
  cases x with
  | zero => cases y <;> simp [op, f, parity, up, down]
  | odd n =>
      cases n with
      | zero => cases y <;> simp [op, f, parity, up, down]
      | succ n => cases y <;> simp [op, f, parity, up, down]
  | even n => cases y <;> simp [op, f, parity, up, down]

theorem target_not :
    ¬ ∀ x y : R, x = op (op (op y y) y) (op (op y y) x) := by
  intro h
  have bad := h .zero .zero
  exact R.noConfusion bad

end CM14746_24393

def certificate : Goal := by
  refine ⟨CM14746_24393.R, ⟨CM14746_24393.op⟩, ?_, ?_⟩
  · exact CM14746_24393.source
  · exact CM14746_24393.target_not

end submission

def submission : Goal := submission.certificate

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_14746_to_24393 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_14746_to_24393
