-- Equation12820 → Equation4399
-- Recorded verdict: false
-- Premise: x = y ◇ ((x ◇ (x ◇ (z ◇ z))) ◇ y)
-- Conclusion: x ◇ (x ◇ y) = (x ◇ y) ◇ y
-- Original submission SHA-256: 111de7113e935115a784bdcd2e2eac16b40de4a7190b607684aeea96865c6dce
-- Aurora-accepted correction SHA-256: 18f29ff7e251a9380dd50c2282c1fe7d94cd7c9c6548f59a63ccd5d2dd7087c4
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ ((x ◇ (x ◇ (z ◇ z))) ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ (x ◇ y) = (x ◇ y) ◇ y
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Aurora-accepted corrected submission body
                   

namespace submission

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Countermodel12820To4399

@[reducible] def counterMagma : Magma (Fin 26) :=
  magmaFin 26 [
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
    8, 0, 12, 18, 25, 10, 5, 13, 21, 7, 6, 24, 4, 14, 11, 9, 3, 2, 15, 1, 23, 16, 20, 22, 17, 19,
    10, 5, 0, 22, 6, 14, 9, 18, 20, 21, 4, 13, 8, 24, 15, 1, 2, 23, 12, 25, 7, 11, 16, 3, 19, 17,
    7, 9, 20, 0, 5, 1, 12, 6, 4, 24, 18, 14, 21, 25, 23, 3, 17, 22, 8, 11, 19, 13, 10, 2, 15, 16,
    2, 17, 16, 23, 0, 7, 10, 25, 9, 11, 22, 6, 19, 5, 1, 12, 15, 3, 20, 13, 24, 18, 4, 14, 21, 8,
    13, 7, 11, 21, 19, 0, 25, 2, 3, 22, 8, 23, 14, 18, 10, 17, 12, 6, 4, 9, 1, 20, 15, 5, 16, 24,
    3, 16, 23, 15, 17, 8, 0, 24, 22, 10, 2, 4, 7, 20, 19, 14, 18, 25, 21, 5, 11, 12, 9, 1, 6, 13,
    24, 11, 13, 9, 20, 25, 7, 0, 17, 1, 14, 19, 18, 8, 21, 6, 22, 15, 10, 4, 16, 23, 5, 12, 3, 2,
    25, 4, 19, 13, 7, 6, 17, 5, 0, 2, 9, 12, 23, 22, 18, 20, 14, 24, 16, 21, 10, 8, 3, 15, 11, 1,
    17, 24, 25, 16, 1, 15, 4, 8, 6, 0, 3, 2, 11, 21, 9, 5, 23, 12, 19, 18, 14, 10, 13, 20, 7, 22,
    22, 23, 3, 17, 10, 9, 8, 16, 13, 25, 0, 15, 6, 12, 24, 21, 4, 1, 7, 20, 18, 19, 2, 11, 5, 14,
    23, 20, 17, 14, 3, 11, 2, 21, 12, 16, 1, 0, 25, 10, 7, 22, 19, 9, 5, 24, 4, 6, 18, 13, 8, 15,
    9, 15, 6, 1, 8, 19, 22, 3, 10, 14, 5, 17, 0, 4, 13, 16, 21, 20, 24, 2, 12, 7, 11, 25, 18, 23,
    11, 14, 21, 19, 9, 2, 20, 1, 24, 12, 23, 5, 22, 0, 8, 4, 6, 16, 13, 15, 3, 17, 25, 18, 10, 7,
    12, 2, 18, 6, 15, 16, 21, 23, 11, 17, 13, 8, 20, 9, 0, 10, 1, 14, 25, 3, 5, 24, 19, 7, 22, 4,
    6, 10, 4, 7, 11, 17, 24, 15, 5, 8, 12, 21, 2, 16, 3, 0, 9, 13, 1, 14, 25, 22, 23, 19, 20, 18,
    4, 12, 10, 8, 22, 18, 11, 19, 1, 6, 16, 20, 13, 15, 25, 2, 0, 7, 3, 23, 21, 9, 24, 17, 14, 5,
    20, 22, 8, 2, 18, 21, 13, 4, 15, 23, 19, 1, 17, 6, 12, 24, 11, 0, 14, 16, 9, 5, 7, 10, 25, 3,
    5, 6, 1, 4, 13, 23, 19, 22, 7, 15, 24, 18, 10, 11, 20, 8, 25, 21, 0, 17, 2, 3, 14, 16, 9, 12,
    21, 8, 9, 12, 24, 3, 18, 14, 19, 13, 15, 7, 16, 2, 6, 11, 20, 5, 17, 0, 22, 25, 1, 4, 23, 10,
    14, 13, 5, 11, 23, 12, 15, 10, 16, 20, 25, 3, 9, 1, 17, 19, 24, 18, 22, 7, 0, 4, 21, 8, 2, 6,
    1, 19, 15, 5, 14, 20, 23, 9, 25, 4, 17, 10, 3, 7, 16, 18, 8, 11, 2, 22, 13, 0, 6, 24, 12, 21,
    16, 21, 22, 25, 2, 24, 1, 20, 18, 3, 7, 9, 15, 17, 5, 13, 10, 19, 23, 12, 8, 14, 0, 6, 4, 11,
    18, 3, 7, 10, 21, 13, 16, 12, 14, 19, 20, 22, 24, 23, 2, 25, 5, 4, 11, 6, 17, 15, 8, 0, 1, 9,
    15, 18, 14, 24, 16, 22, 3, 17, 23, 5, 11, 25, 1, 19, 4, 7, 13, 8, 9, 10, 6, 2, 12, 21, 0, 20,
    19, 25, 24, 20, 12, 4, 14, 11, 2, 18, 21, 16, 5, 3, 22, 23, 7, 10, 6, 8, 15, 1, 17, 9, 13, 0
  ]

local instance : Magma (Fin 26) := counterMagma

theorem diagonal : ∀ z : Fin 26, z ◇ z = 0 := by
  decide

theorem core : ∀ x y : Fin 26,
    x = y ◇ ((x ◇ (x ◇ (0 : Fin 26))) ◇ y) := by
  decide

theorem source : EquationLHS (Fin 26) := by
  intro x y z
  rw [diagonal z]
  exact core x y

theorem target_false : ¬ EquationRHS (Fin 26) := by
  decide

end Countermodel12820To4399

def certificate : Goal :=
  ⟨Fin 26, Countermodel12820To4399.counterMagma,
    Countermodel12820To4399.source, Countermodel12820To4399.target_false⟩

end submission

def submission : Goal := submission.certificate

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_12820_to_4399 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_12820_to_4399
