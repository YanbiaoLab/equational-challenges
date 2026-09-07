-- Equation33419 → Equation519
-- Recorded verdict: false
-- Premise: x = (y ◇ (((z ◇ z) ◇ x) ◇ x)) ◇ y
-- Conclusion: x = y ◇ (y ◇ (y ◇ (z ◇ w)))
-- Original submission SHA-256: 360eb373debcc9ed2a40d1ea1d040668a177bb354783716f3331022f7cb7a314
-- Aurora-accepted correction SHA-256: 0212a31a52c1cebdeb6d6ce54ca655d3b0f5e75b3672da41af85df1468ff9b7b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (((z ◇ z) ◇ x) ◇ x)) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ (y ◇ (y ◇ (z ◇ w)))
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Aurora-accepted corrected submission body
                   

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace submission

namespace Countermodel33419To519

@[reducible] def counterMagma : Magma (Fin 26) :=
  magmaFin 26 [
    0, 8, 10, 7, 2, 13, 3, 24, 25, 17, 22, 23, 9, 11, 12, 6, 4, 20, 5, 21, 14, 1, 16, 18, 15, 19,
    1, 0, 5, 9, 17, 7, 16, 11, 4, 24, 23, 20, 15, 14, 2, 10, 12, 22, 6, 8, 13, 19, 21, 3, 18, 25,
    2, 12, 0, 20, 16, 11, 23, 13, 19, 25, 3, 17, 6, 21, 18, 4, 10, 8, 1, 9, 5, 15, 22, 7, 14, 24,
    3, 18, 22, 0, 23, 21, 15, 9, 13, 16, 17, 14, 1, 19, 6, 7, 8, 2, 4, 12, 11, 5, 25, 10, 24, 20,
    4, 25, 6, 5, 0, 19, 17, 20, 7, 1, 10, 3, 8, 9, 15, 11, 22, 18, 13, 24, 23, 14, 2, 21, 16, 12,
    5, 10, 14, 1, 7, 0, 8, 25, 6, 15, 9, 11, 19, 2, 16, 17, 18, 21, 23, 3, 12, 20, 24, 13, 22, 4,
    6, 5, 9, 12, 10, 25, 0, 7, 17, 4, 8, 2, 22, 20, 21, 24, 11, 13, 19, 18, 15, 23, 1, 16, 3, 14,
    7, 13, 18, 6, 25, 2, 24, 0, 5, 8, 16, 21, 3, 1, 23, 15, 19, 4, 22, 14, 10, 9, 20, 12, 17, 11,
    8, 21, 20, 4, 9, 3, 22, 17, 0, 6, 13, 12, 10, 24, 11, 5, 1, 15, 7, 19, 16, 25, 18, 14, 23, 2,
    9, 7, 21, 24, 11, 22, 10, 1, 2, 0, 25, 16, 14, 12, 17, 8, 6, 23, 15, 13, 20, 4, 3, 19, 5, 18,
    10, 6, 4, 18, 22, 8, 2, 14, 9, 3, 0, 1, 5, 23, 13, 12, 16, 19, 24, 15, 25, 17, 7, 20, 11, 21,
    11, 24, 13, 14, 6, 23, 4, 19, 12, 2, 15, 0, 17, 5, 8, 21, 20, 1, 18, 7, 3, 10, 9, 22, 25, 16,
    12, 4, 8, 21, 19, 14, 7, 18, 23, 11, 6, 25, 0, 22, 20, 2, 13, 17, 10, 16, 9, 3, 15, 24, 1, 5,
    13, 14, 24, 25, 5, 18, 20, 8, 22, 21, 12, 10, 4, 0, 9, 16, 15, 6, 11, 2, 1, 7, 17, 23, 19, 3,
    14, 11, 15, 23, 1, 10, 19, 21, 18, 9, 24, 7, 13, 8, 0, 3, 25, 12, 20, 6, 17, 16, 5, 2, 4, 22,
    15, 9, 1, 3, 12, 17, 14, 6, 20, 5, 21, 22, 16, 4, 10, 0, 2, 24, 8, 11, 19, 18, 13, 25, 7, 23,
    16, 3, 2, 17, 15, 12, 18, 22, 14, 23, 4, 19, 21, 6, 1, 9, 0, 11, 25, 20, 24, 8, 10, 5, 13, 7,
    17, 2, 23, 22, 3, 6, 25, 15, 24, 12, 1, 9, 20, 16, 14, 13, 7, 0, 21, 5, 18, 11, 19, 4, 8, 10,
    18, 15, 12, 8, 20, 4, 21, 10, 16, 19, 7, 5, 24, 13, 25, 1, 3, 14, 0, 17, 22, 2, 23, 11, 9, 6,
    19, 1, 25, 11, 13, 9, 5, 4, 21, 18, 20, 24, 2, 15, 3, 14, 23, 16, 17, 0, 7, 22, 12, 6, 10, 8,
    20, 23, 7, 19, 24, 1, 11, 16, 10, 14, 18, 4, 12, 3, 5, 25, 21, 9, 2, 22, 0, 13, 8, 17, 6, 15,
    21, 16, 11, 13, 18, 20, 12, 23, 8, 10, 19, 6, 7, 17, 24, 22, 9, 5, 3, 25, 4, 0, 14, 15, 2, 1,
    22, 20, 16, 10, 4, 15, 9, 5, 3, 13, 2, 18, 11, 25, 19, 23, 24, 7, 14, 1, 21, 6, 0, 8, 12, 17,
    23, 22, 3, 2, 14, 5, 1, 12, 15, 20, 11, 13, 25, 18, 7, 19, 17, 10, 16, 4, 8, 24, 6, 0, 21, 9,
    24, 17, 19, 15, 21, 16, 6, 3, 11, 7, 5, 8, 18, 10, 22, 20, 14, 25, 9, 23, 2, 12, 4, 1, 0, 13,
    25, 19, 17, 16, 8, 24, 13, 2, 1, 22, 14, 15, 23, 7, 4, 18, 5, 3, 12, 10, 6, 21, 11, 9, 20, 0
  ]

local instance : Magma (Fin 26) := counterMagma

theorem diagonal : ∀ z : Fin 26, z ◇ z = 0 := by
  decide

theorem core : ∀ x y : Fin 26,
    x = (y ◇ (((0 : Fin 26) ◇ x) ◇ x)) ◇ y := by
  decide

theorem source : EquationLHS (Fin 26) := by
  intro x y z
  rw [diagonal z]
  exact core x y

theorem target_false : ¬ EquationRHS (Fin 26) := by
  decide

end Countermodel33419To519

end submission


def submission : Goal :=
  ⟨Fin 26, submission.Countermodel33419To519.counterMagma,
    submission.Countermodel33419To519.source, submission.Countermodel33419To519.target_false⟩

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_33419_to_519 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_33419_to_519
