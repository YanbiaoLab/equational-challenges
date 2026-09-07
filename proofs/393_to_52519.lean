-- Equation393 → Equation52519
-- Recorded verdict: true
-- Premise: x * y = (y * z) * w
-- Conclusion: x * y = ((y * (z * z)) * y) * x
-- Original submission SHA-256: 111462a143cde9df107141f7eaed739fadb87448d8617c8841348cdfff637a72
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (y ◇ z) ◇ w
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((y ◇ (z ◇ z)) ◇ y) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3 q4 q5:G), (((q5 ◇ q1) ◇ q0) ◇ q2) = (q3 ◇ q4):=by
    intro q0 q1 q2 q3 q4 q5
    exact ((congrArg (fun t => t ◇ q2) (h q4 q5 q1 q0)).symm).trans ((h q3 q4 q5 q2).symm)
  have apc1 : forall (x y z w:G), (y ◇ y) = (x ◇ y):=by
    intro x y z w
    exact ((h x y z w).trans ((h y y z w).symm)).symm
  have apc2 : forall (q6 q7 q8 q9 q10:G), (((q7 ◇ q7) ◇ q6) ◇ q8) = (q9 ◇ q10):=by
    intro q6 q7 q8 q9 q10
    exact ((congrArg (fun t => t ◇ q8) (congrArg (fun t => t ◇ q6) ((apc1 q6 q7 q6 q6).symm))).symm).trans (apc0 q6 q7 q8 q9 q10 q6)
  have apc5 : forall (x y z w:G), ((y ◇ z) ◇ w) = ((y ◇ x) ◇ x):=by
    intro x y z w
    exact ((h x y z w).symm).trans (h x y x x)
  have apc7 : forall (q11 q12 q13 q14 q15:G), (((q12 ◇ q11) ◇ q11) ◇ q13) = (q14 ◇ q15):=by
    intro q11 q12 q13 q14 q15
    exact ((congrArg (fun t => t ◇ q13) (apc5 q11 q12 q12 q11)).symm).trans (apc2 q11 q12 q13 q14 q15)
  have apc8 : forall (q16 q17 q18 q19:G), (((q16 ◇ q16) ◇ q16) ◇ q17) = (q18 ◇ q19):=by
    intro q16 q17 q18 q19
    exact ((congrArg (fun t => t ◇ q17) (congrArg (fun t => t ◇ q16) ((apc1 q16 q16 q16 q16).symm))).symm).trans (apc7 q16 q16 q17 q18 q19)
  exact ((apc8 (x ◇ y) (((y ◇ (z ◇ z)) ◇ y) ◇ x) x y).symm).trans (apc8 (x ◇ y) (((y ◇ (z ◇ z)) ◇ y) ◇ x) ((y ◇ (z ◇ z)) ◇ y) x)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_393_to_52519 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_393_to_52519
