-- Equation53529 → Equation51205
-- Recorded verdict: true
-- Premise: x * y = (((z * y) * y) * x) * x
-- Conclusion: x * x = ((x * y) * (y * y)) * y
-- Original submission SHA-256: 67371da3dc95dd8440f7fc1a0d8419d3193f1c4b8540cf2fa055fff39bd6b5a2
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (((z ◇ y) ◇ y) ◇ x) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ x = ((x ◇ y) ◇ (y ◇ y)) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc1 : forall (q0 q1 q2:G), (((q2 ◇ q0) ◇ q1) ◇ q1) = (q1 ◇ q2):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ q1) (congrArg (fun t => t ◇ q1) ((h q2 q0 q0).symm))).symm).trans ((h q1 q2 ((q0 ◇ q0) ◇ q0)).symm)
  have apc2 : forall (q3 q4 q5:G), (q3 ◇ (q5 ◇ q4)) = (q3 ◇ q4):=by
    intro q3 q4 q5
    exact ((apc1 q4 q3 (q5 ◇ q4)).symm).trans ((h q3 q4 q5).symm)
  have apc6 : forall (q6 q7 q8 q9:G), ((q7 ◇ q6) ◇ q8) = (q6 ◇ q8):=by
    intro q6 q7 q8 q9
    exact ((((congrArg (fun t => t ◇ q6) (apc2 (q8 ◇ q9) q6 q7)).trans (apc1 q9 q6 q8)).symm).trans (((apc2 ((q8 ◇ q9) ◇ (q7 ◇ q6)) q6 q7).symm).trans (apc1 q9 (q7 ◇ q6) q8))).symm
  have apc7 : forall (q10 q11 q12:G), (q11 ◇ q12) = (q10 ◇ q12):=by
    intro q10 q11 q12
    exact (((apc6 q10 q11 q12 ((q11 ◇ q10) ◇ q12)).symm).trans (((congrArg (fun t => t ◇ q12) ((h q11 q10 q10).symm)).symm).trans (apc6 q11 (((q10 ◇ q10) ◇ q10) ◇ q11) q12 q10))).symm
  have apc9 : forall (q13 q14 q15:G), (q14 ◇ q15) = (q13 ◇ q14):=by
    intro q13 q14 q15
    exact (((apc7 q13 (((q13 ◇ q15) ◇ q15) ◇ q14) q14).symm).trans ((h q14 q15 q13).symm)).symm
  exact (apc9 y x x).trans (apc9 ((x ◇ y) ◇ (y ◇ y)) y x)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_53529_to_51205 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_53529_to_51205
