-- Equation47260 → Equation3301
-- Recorded verdict: true
-- Premise: x * y = (y * z) * ((z * y) * w)
-- Conclusion: x * x = y * (z * (w * y))
-- Original submission SHA-256: 09792c9330f423b74a3749f5d63d5f128bb27b9df405941d40dae11a188c3a69
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (y ◇ z) ◇ ((z ◇ y) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = y ◇ (z ◇ (w ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w:G), (y ◇ y) = (x ◇ y):=by
    intro x y z w
    exact ((h x y z w).trans ((h y y z w).symm)).symm
  have apc1 : forall (q0 q1 q2:G), (q1 ◇ q2) = (q0 ◇ q2):=by
    intro q0 q1 q2
    exact ((h q0 q2 q0 q0).trans ((h q1 q2 q0 q0).symm)).symm
  have apc2 : forall (q3 q4 q5 q6:G), ((q5 ◇ q6) ◇ (q3 ◇ (q6 ◇ q5))) = (q4 ◇ q5):=by
    intro q3 q4 q5 q6
    exact ((congrArg (fun t => (q5 ◇ q6) ◇ t) (apc0 q3 (q6 ◇ q5) q3 q3)).symm).trans ((h q4 q5 q6 (q6 ◇ q5)).symm)
  have apc3 : forall (q7 q8 q9 q10 q11:G), (q11 ◇ (q7 ◇ (q10 ◇ q9))) = (q8 ◇ q9):=by
    intro q7 q8 q9 q10 q11
    exact (((apc2 q7 q8 q9 q10).symm).trans (apc1 q11 (q9 ◇ q10) (q7 ◇ (q10 ◇ q9)))).symm
  have apc4 : forall (q12 q13 q14 q15:G), (q14 ◇ (q12 ◇ (q13 ◇ q15))) = (q15 ◇ q15):=by
    intro q12 q13 q14 q15
    exact (apc3 q12 q12 q15 q13 q14).trans ((apc0 q12 q15 q12 q12).symm)
  have apc11 : forall (q16 q17 q18:G), (q17 ◇ q18) = (q16 ◇ q16):=by
    intro q16 q17 q18
    exact (((apc4 (q16 ◇ q18) q16 (q18 ◇ q16) q16).symm).trans ((h q17 q18 q16 (q16 ◇ q16)).symm)).symm
  exact (apc11 (x ◇ x) x x).trans ((apc11 (x ◇ x) y (z ◇ (w ◇ y))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_47260_to_3301 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_47260_to_3301
