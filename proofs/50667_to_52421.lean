-- Equation50667 → Equation52421
-- Recorded verdict: false
-- Premise: x ◇ y = (y ◇ ((x ◇ y) ◇ y)) ◇ y
-- Conclusion: x ◇ y = ((y ◇ (x ◇ y)) ◇ y) ◇ y
-- Original submission SHA-256: 0d91c3a5b628029de09c61341b689794e468c8903b66cb886aeabc0404354e4b
-- Generator: equational-challenges standalone v1
-- All project definitions are embedded in this file.
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.SplitIfs

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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ y = (y ◇ ((x ◇ y) ◇ y)) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ y = ((y ◇ (x ◇ y)) ◇ y) ◇ y
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Original submission body
                   
                             
                              
namespace submission
inductive C | c0 | c1 deriving DecidableEq
def ctrl : C → C → C
  | .c0, .c0 => .c0
  | .c0, .c1 => .c0
  | .c1, .c0 => .c0
  | .c1, .c1 => .c0
def guard : C → C → Bool
  | .c0, .c0 => true
  | .c0, .c1 => false
  | .c1, .c0 => true
  | .c1, .c1 => false
abbrev M := Nat × C
def op (a b : M) : M :=
  (if guard a.2 b.2 then b.1 - 2 else a.1 + 1,
   ctrl a.2 b.2)
instance instMagma : Magma M where op := op
theorem source_holds : @EquationLHS M instMagma := by
  intro q0 q1
  change (op q0 q1) = (op (op q1 (op (op q0 q1) q1)) q1)
  rcases q0 with ⟨n0, s0⟩
  rcases q1 with ⟨n1, s1⟩
  cases s0 <;> cases s1 <;>
    simp [op, ctrl, guard] <;> (try split_ifs) <;> omega
theorem target_fails : ¬ @EquationRHS M instMagma := by
  intro target
  have bad := target ((0, .c0) : M) ((0, .c1) : M)
  exact (by decide : (op ((0, .c0) : M) ((0, .c1) : M)) ≠ (op (op (op ((0, .c1) : M) (op ((0, .c0) : M) ((0, .c1) : M))) ((0, .c1) : M)) ((0, .c1) : M))) bad
end submission
def submission : Goal :=
  ⟨submission.M, submission.instMagma,
   submission.source_holds, submission.target_fails⟩

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_50667_to_52421 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_50667_to_52421
