-- Equation52770 → Equation4441
-- Recorded verdict: true
-- Premise: x * y = ((z * (z * w)) * y) * z
-- Conclusion: x * (y * x) = (x * z) * w
-- Original submission SHA-256: e054fa803511984e45310c21b6a7ff56e3b66fab19e09897cc6b81bebbee766e
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ (z ◇ w)) ◇ y) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ x) = (x ◇ z) ◇ w
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w:G), (y ◇ y) = (x ◇ y):=by
    intro x y z w
    exact ((h x y z w).trans ((h y y z w).symm)).symm
  have apc1 : forall (q0 q1 q2:G), ((q1 ◇ q1) ◇ q2) = (q0 ◇ q1):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ q2) ((apc0 (q2 ◇ (q2 ◇ q0)) q1 q0 q0).symm)).symm).trans ((h q0 q1 q2 q0).symm)
  have apc12 : forall (q3 q4 q5 q6:G), ((q3 ◇ q5) ◇ q6) = (q4 ◇ q5):=by
    intro q3 q4 q5 q6
    exact ((congrArg (fun t => t ◇ q6) (apc0 q3 q5 q3 q3)).symm).trans (apc1 q4 q5 q6)
  have apc14 : forall (q7 q8 q9:G), ((q7 ◇ q9) ◇ q8) = (q9 ◇ q9):=by
    intro q7 q8 q9
    exact (apc12 q7 q7 q9 q8).trans ((apc0 q7 q9 q7 q7).symm)
  have apc17 : forall (q10 q11 q12 q13 q14:G), (q11 ◇ q12) = (q10 ◇ q10):=by
    intro q10 q11 q12 q13 q14
    exact ((((((congrArg (fun t => t ◇ (q12 ◇ (q12 ◇ q10))) (congrArg (fun t => q13 ◇ t) (apc14 q12 q14 (q12 ◇ q10)))).trans (congrArg (fun t => t ◇ (q12 ◇ (q12 ◇ q10))) (congrArg (fun t => q13 ◇ t) (apc14 q12 (q12 ◇ q10) q10)))).trans (apc14 q13 (q12 ◇ (q12 ◇ q10)) (q10 ◇ q10))).trans (apc14 q10 (q10 ◇ q10) q10)).symm).trans (((congrArg (fun t => t ◇ (q12 ◇ (q12 ◇ q10))) ((h q13 ((q12 ◇ (q12 ◇ q10)) ◇ q14) q12 q10).symm)).symm).trans ((h q11 q12 (q12 ◇ (q12 ◇ q10)) q14).symm))).symm
  exact (apc17 (x ◇ (y ◇ x)) x (y ◇ x) (x ◇ (y ◇ x)) (x ◇ (y ◇ x))).trans ((apc17 (x ◇ (y ◇ x)) (x ◇ z) w (x ◇ (y ◇ x)) (x ◇ (y ◇ x))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_52770_to_4441 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_52770_to_4441
