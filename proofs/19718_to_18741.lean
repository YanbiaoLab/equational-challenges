-- Equation19718 → Equation18741
-- Recorded verdict: false
-- Premise: x = (x ◇ y) ◇ ((y ◇ (z ◇ y)) ◇ y)
-- Conclusion: x = (x ◇ x) ◇ ((x ◇ y) ◇ (z ◇ w))
-- Original submission SHA-256: c0e188d4aa24cee8dfe955993394d2c00e3db16fc68b59075070d877e0886d91
-- Aurora-accepted correction SHA-256: 99245d2deefc5468aeb91d57a0579b82e9d7ae0a3481313a405166ceb8f51307
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ y) ◇ ((y ◇ (z ◇ y)) ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (x ◇ x) ◇ ((x ◇ y) ◇ (z ◇ w))
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Aurora-accepted corrected submission body
                   

namespace submission

namespace CM19718_18741

def op (x y : Nat) : Nat :=
  match x with
  | 0 => if y % 2 = 0 then 0 else 2
  | 1 => if y % 2 = 0 then 1 else 3
  | 2 => if y % 2 = 0 then 2 else 0
  | 3 => if y % 2 = 0 then 4 else 1
  | n + 4 => if x % 2 = y % 2 then n + 3 else n + 5

def instMagma : Magma Nat where
  op := op

theorem eq1661 (x y z : Nat) :
    x = op (op x y) (op (op y z) y) := by
  have right_congr (a b c : Nat) (h : b % 2 = c % 2) :
      op a b = op a c := by
    match a with
    | 0 | 1 | 2 | 3 => simp [op, h]
    | n + 4 => simp [op, h]
  have involutive (a b : Nat) : op (op a b) b = a := by
    match a with
    | 0 | 1 | 2 | 3 | 4 =>
        by_cases h : b % 2 = 0
        · simp [op, h]
        · have hb : b % 2 = 1 := Nat.mod_two_ne_zero.mp h
          simp [op, h, hb]
    | n + 5 =>
        by_cases h : (n + 5) % 2 = b % 2
        · have h' : (n + 4) % 2 ≠ b % 2 := by omega
          simp [op, h, h']
        · have h' : (n + 6) % 2 = b % 2 := by omega
          simp [op, h, h']
  have right_parity (a b : Nat) :
      op (op a b) a % 2 = a % 2 := by
    match a with
    | 0 | 1 | 2 | 3 | 4 =>
        by_cases h : b % 2 = 0
        · simp [op, h]
        · have hb : b % 2 = 1 := Nat.mod_two_ne_zero.mp h
          simp [op, h, hb]
    | n + 5 =>
        by_cases h : (n + 5) % 2 = b % 2
        · have h' : (n + 1 + 3) % 2 ≠ b % 2 := by omega
          simp [op, h, h']
        · have h' : (n + 2 + 4) % 2 ≠ (n + 5) % 2 := by omega
          simp [op, h, h']
          omega
  rw [right_congr (op x y) (op (op y z) y) y (right_parity y z)]
  exact (involutive x y).symm

theorem source (x y z : Nat) :
    x = op (op x y) (op (op y (op z y)) y) := by
  exact eq1661 x y (op z y)

theorem target_not :
    ¬ ∀ x y z w : Nat,
      x = op (op x x) (op (op x y) (op z w)) := by
  intro h
  have bad := h 1 1 0 0
  exact (by decide :
    (1 : Nat) ≠ op (op 1 1) (op (op 1 1) (op 0 0))) bad

end CM19718_18741

end submission


def submission : Goal := by
  refine ⟨Nat, submission.CM19718_18741.instMagma, ?_, ?_⟩
  · intro x y z
    exact submission.CM19718_18741.source x y z
  · exact submission.CM19718_18741.target_not

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_19718_to_18741 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_19718_to_18741
