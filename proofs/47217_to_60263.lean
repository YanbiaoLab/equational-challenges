-- Equation47217 → Equation60263
-- Recorded verdict: true
-- Premise: x * y = (y * y) * ((z * w) * w)
-- Conclusion: (x * y) * x = (z * z) * (y * z)
-- Original submission SHA-256: aa933a20ebfb6fdfa8bd5bbc3c54fe520d932c1c9a749bbfded792c5a2c52b02
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (y ◇ y) ◇ ((z ◇ w) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ x = (z ◇ z) ◇ (y ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z w:G), (y ◇ y) = (x ◇ y):=by
    intro x y z w
    exact ((h x y z w).trans ((h y y z w).symm)).symm
  have apc1 : forall (q0 q1 q2:G), ((q2 ◇ q2) ◇ (q0 ◇ q0)) = (q1 ◇ q2):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => (q2 ◇ q2) ◇ t) ((apc0 (q0 ◇ q0) q0 q0 q0).symm)).symm).trans ((h q1 q2 q0 q0).symm)
  have apc2 : forall (q3 q4:G), ((q4 ◇ q4) ◇ (q3 ◇ q3)) = (q4 ◇ q4):=by
    intro q3 q4
    exact (apc1 q3 q3 q4).trans ((apc0 q3 q4 q3 q3).symm)
  have apc3 : forall (q5 q6 q7:G), ((q7 ◇ q7) ◇ (q5 ◇ q6)) = (q7 ◇ q7):=by
    intro q5 q6 q7
    exact ((congrArg (fun t => (q7 ◇ q7) ◇ t) (apc0 q5 q6 q5 q5)).symm).trans (apc2 q6 q7)
  have apc6 : forall (q8 q9 q10 q11:G), ((q8 ◇ q11) ◇ (q9 ◇ q10)) = (q11 ◇ q11):=by
    intro q8 q9 q10 q11
    exact ((congrArg (fun t => t ◇ (q9 ◇ q10)) (apc0 q8 q11 q8 q8)).symm).trans (apc3 q9 q10 q11)
  have apc10 : forall (q12 q13 q14 q15 q16:G), (q14 ◇ (q12 ◇ q13)) = (q13 ◇ q13):=by
    intro q12 q13 q14 q15 q16
    exact (((apc6 q13 (q15 ◇ q16) q16 q13).symm).trans (((congrArg (fun t => t ◇ ((q15 ◇ q16) ◇ q16)) (apc6 q12 q12 q13 q13)).symm).trans ((h q14 (q12 ◇ q13) q15 q16).symm))).symm
  have apc11 : forall (q0 q1 q2 q17 q18:G), (q1 ◇ q2) = (q0 ◇ q0):=by
    intro q0 q1 q2 q17 q18
    exact (((apc10 (q17 ◇ q0) q0 (q18 ◇ q2) ((q18 ◇ q2) ◇ ((q17 ◇ q0) ◇ q0)) ((q18 ◇ q2) ◇ ((q17 ◇ q0) ◇ q0))).symm).trans (((congrArg (fun t => t ◇ ((q17 ◇ q0) ◇ q0)) (apc0 q18 q2 q18 q18)).symm).trans ((h q1 q2 q17 q0).symm))).symm
  exact (apc11 ((x ◇ y) ◇ x) (x ◇ y) x ((x ◇ y) ◇ x) ((x ◇ y) ◇ x)).trans ((apc11 ((x ◇ y) ◇ x) (z ◇ z) (y ◇ z) ((x ◇ y) ◇ x) ((x ◇ y) ◇ x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_47217_to_60263 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_47217_to_60263
