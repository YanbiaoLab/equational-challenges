-- Equation47568 → Equation42469
-- Recorded verdict: true
-- Premise: x * y = (z * w) * ((y * w) * x)
-- Conclusion: x * x = y * (x * ((y * x) * y))
-- Original submission SHA-256: 4452f2353ce8d5f7e0abd32e3b3360b4bb4154a56faddf7fa83c8150871aa113
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ w) ◇ ((y ◇ w) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ x = y ◇ (x ◇ ((y ◇ x) ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (q0 q1 q2 q3 q4:G), (((q1 ◇ q2) ◇ q0) ◇ q3) = ((q4 ◇ q2) ◇ (q0 ◇ q1)):=by
    intro q0 q1 q2 q3 q4
    exact (((congrArg (fun t => (q4 ◇ q2) ◇ t) ((h q0 q1 q3 q2).symm)).symm).trans ((h ((q1 ◇ q2) ◇ q0) q3 q4 q2).symm)).symm
  have apc1 : forall (q5 q6 q7 q8 q9 q10:G), ((q7 ◇ q6) ◇ (q8 ◇ q5)) = (q9 ◇ q10):=by
    intro q5 q6 q7 q8 q9 q10
    exact ((apc0 q8 q5 q6 ((q10 ◇ q8) ◇ q9) q7).symm).trans ((h q9 q10 (q5 ◇ q6) q8).symm)
  have apc2 : forall (q5 q6 q7 q8 q9 q10:G), (q9 ◇ q10) = (q5 ◇ q5):=by
    intro q5 q6 q7 q8 q9 q10
    exact ((apc1 q5 q6 q7 q8 q9 q10).symm).trans (apc1 q5 q6 q7 q8 q5 q5)
  exact (apc2 (x ◇ x) (x ◇ x) (x ◇ x) (x ◇ x) x x).trans ((apc2 (x ◇ x) (x ◇ x) (x ◇ x) (x ◇ x) y (x ◇ ((y ◇ x) ◇ y))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_47568_to_42469 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_47568_to_42469
