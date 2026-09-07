-- Equation54217 → Equation54169
-- Recorded verdict: true
-- Premise: x ◇ (y ◇ y) = y ◇ (y ◇ (z ◇ w))
-- Conclusion: x ◇ (y ◇ y) = x ◇ (x ◇ (z ◇ z))
-- Original submission SHA-256: a67301d9e8efd3c250ebb31c4fecf976a1f896f681cb1e920e808b3c552b4235
-- Generator: equational-challenges standalone v1
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ y) = y ◇ (y ◇ (z ◇ w))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ y) = x ◇ (x ◇ (z ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z w:G), (y ◇ (y ◇ y)) = (x ◇ (y ◇ y)):=by
    intro x y z w
    exact ((h x y x x).trans ((h y y x x).symm)).symm
  have apc1 : forall (q0 q1 q2:G), (q1 ◇ (q2 ◇ q2)) = (q0 ◇ (q2 ◇ q2)):=by
    intro q0 q1 q2
    exact ((h q0 q2 q0 q0).trans ((h q1 q2 q0 q0).symm)).symm
  have apc3 : forall (x y z w:G), (y ◇ (y ◇ (z ◇ w))) = (y ◇ (y ◇ (x ◇ x))):=by
    intro x y z w
    exact ((h x y z w).symm).trans (h x y x x)
  have apc6 : forall (q3 q4 q5:G), (q4 ◇ (q4 ◇ (q5 ◇ q3))) = (q4 ◇ (q4 ◇ q4)):=by
    intro q3 q4 q5
    exact ((apc0 q3 q4 q3 q3).trans (h q3 q4 q5 q3)).symm
  have apc10 : forall (q6 q7 q8:G), (q8 ◇ (q6 ◇ (q7 ◇ q7))) = (q8 ◇ (q8 ◇ q8)):=by
    intro q6 q7 q8
    exact (((congrArg (fun t => q8 ◇ t) (apc1 q6 q8 q7)).symm).trans (apc3 q6 q8 q7 q7)).trans (apc6 q6 q8 q6)
  have apc11 : forall (q9 q10:G), (q10 ◇ (q10 ◇ q10)) = (q9 ◇ (q9 ◇ q9)):=by
    intro q9 q10
    exact (((apc10 (q9 ◇ q9) q9 q10).symm).trans (apc1 q9 q10 (q9 ◇ q9))).trans (apc10 (q9 ◇ q9) q9 q9)
  have apc12 : forall (q11 q12 q13:G), (q12 ◇ (q13 ◇ q13)) = (q11 ◇ (q11 ◇ q11)):=by
    intro q11 q12 q13
    exact (((apc11 q11 q13).symm).trans (apc0 q12 q13 q11 q11)).symm
  have apc13 : forall (q14 q15 q16 q17:G), (q16 ◇ (q17 ◇ q17)) = (q14 ◇ (q15 ◇ q15)):=by
    intro q14 q15 q16 q17
    exact ((apc12 q17 q14 q15).trans (apc0 q16 q17 q14 q14)).symm
  exact (calc
    (x ◇ (y ◇ y)) = (y ◇ (x ◇ x)):=apc13 y x x y
    _ = (x ◇ (x ◇ (z ◇ z))):=((h y x z z).symm).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_54217_to_54169 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_54217_to_54169
