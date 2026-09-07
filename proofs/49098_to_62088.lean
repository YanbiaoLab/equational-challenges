-- Equation49098 → Equation62088
-- Recorded verdict: true
-- Premise: x * y = ((z * x) * z) * (w * z)
-- Conclusion: (x * y) * y = ((x * z) * w) * z
-- Original submission SHA-256: 0faa83e2cfd3ffb79329b980ff8555efe7b8df15c52561796e63b03c4561c272
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ x) ◇ z) ◇ (w ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ y = ((x ◇ z) ◇ w) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w
    exact (h x y z w).trans ((h x x z w).symm)
  have apc1 : forall (q0 q1 q2 q3:G), (((q2 ◇ q1) ◇ q2) ◇ (q0 ◇ q0)) = (q1 ◇ q1):=by
    intro q0 q1 q2 q3
    exact (((congrArg (fun t => ((q2 ◇ q1) ◇ q2) ◇ t) (apc0 q0 q2 q0 q0)).symm).trans ((h q1 q3 q2 q0).symm)).trans (apc0 q1 q3 (q1 ◇ q3) (q1 ◇ q3))
  have apc3 : forall (q4 q5 q6 q7 q8:G), (((q4 ◇ q4) ◇ q7) ◇ (q5 ◇ q5)) = (q6 ◇ q6):=by
    intro q4 q5 q6 q7 q8
    exact ((((congrArg (fun t => t ◇ (q5 ◇ q5)) (congrArg (fun t => t ◇ q7) (congrArg (fun t => t ◇ (q8 ◇ q4)) (congrArg (fun t => t ◇ q4) (apc0 q4 q7 (q4 ◇ q7) (q4 ◇ q7)))))).trans (congrArg (fun t => t ◇ (q5 ◇ q5)) (congrArg (fun t => t ◇ q7) (congrArg (fun t => ((q4 ◇ q4) ◇ q4) ◇ t) (apc0 q8 q4 (q8 ◇ q4) (q8 ◇ q4)))))).trans (congrArg (fun t => t ◇ (q5 ◇ q5)) (congrArg (fun t => t ◇ q7) (apc1 q8 q4 q4 (((q4 ◇ q4) ◇ q4) ◇ (q8 ◇ q8)))))).symm).trans (((congrArg (fun t => t ◇ (q5 ◇ q5)) (congrArg (fun t => t ◇ q7) (h q7 q6 q4 q8))).symm).trans (apc1 q5 q6 q7 q8))
  have apc4 : forall (q9 q10 q11:G), (q11 ◇ q11) = (q10 ◇ q9):=by
    intro q9 q10 q11
    exact ((h q10 q9 q10 q10).trans (apc3 q10 q10 q11 q10 q9)).symm
  exact ((apc4 y (x ◇ y) ((x ◇ y) ◇ y)).symm).trans (apc4 z ((x ◇ z) ◇ w) ((x ◇ y) ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_49098_to_62088 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_49098_to_62088
