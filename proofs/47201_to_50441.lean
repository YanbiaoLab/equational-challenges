-- Equation47201 → Equation50441
-- Recorded verdict: true
-- Premise: x * y = (y * y) * ((y * z) * w)
-- Conclusion: x * x = (y * ((z * x) * w)) * u
-- Original submission SHA-256: 7ccff9f094edd3e5875b02adba6b5d5d37619b322d015a2506d52f752bed71e5
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (y ◇ y) ◇ ((y ◇ z) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ x = (y ◇ ((z ◇ x) ◇ w)) ◇ u
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (x y z w:G), (y ◇ y) = (x ◇ y):=by
    intro x y z w
    exact ((h x y z w).trans ((h y y z w).symm)).symm
  have apc2 : forall (q0 q1 q2:G), ((q2 ◇ q2) ◇ (q0 ◇ q2)) = (q1 ◇ q2):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => (q2 ◇ q2) ◇ t) ((h q0 q2 q0 q0).symm)).symm).trans ((h q1 q2 q2 ((q2 ◇ q0) ◇ q0)).symm)
  have apc3 : forall (q3 q4:G), ((q4 ◇ q4) ◇ (q3 ◇ q4)) = (q4 ◇ q4):=by
    intro q3 q4
    exact (apc2 q3 q3 q4).trans ((apc0 q3 q4 q3 q3).symm)
  have apc6 : forall (q5 q6 q7:G), ((q5 ◇ q7) ◇ (q6 ◇ q7)) = (q7 ◇ q7):=by
    intro q5 q6 q7
    exact ((congrArg (fun t => t ◇ (q6 ◇ q7)) (apc0 q5 q7 q5 q5)).symm).trans (apc3 q6 q7)
  have apc7 : forall (q8 q9 q10 q11 q12:G), ((q12 ◇ ((q10 ◇ q11) ◇ q8)) ◇ (q9 ◇ q10)) = (q8 ◇ q8):=by
    intro q8 q9 q10 q11 q12
    exact (((congrArg (fun t => (q12 ◇ ((q10 ◇ q11) ◇ q8)) ◇ t) ((h q9 q10 q11 q8).symm)).symm).trans (apc6 q12 (q10 ◇ q10) ((q10 ◇ q11) ◇ q8))).trans (apc6 (q10 ◇ q11) (q10 ◇ q11) q8)
  have apc10 : forall (q13 q14 q15:G), (q14 ◇ q14) = (q13 ◇ q13):=by
    intro q13 q14 q15
    exact ((((apc7 q13 q15 q14 q13 q13).symm).trans ((apc0 (q13 ◇ ((q14 ◇ q13) ◇ q13)) (q15 ◇ q14) q13 q13).symm)).trans (apc6 q15 q15 q14)).symm
  have apc12 : forall (q16 q17 q18:G), (q17 ◇ q18) = (q16 ◇ q16):=by
    intro q16 q17 q18
    exact (((apc10 q16 q18 q16).symm).trans (apc0 q17 q18 q16 q16)).symm
  exact (apc12 (x ◇ x) x x).trans ((apc12 (x ◇ x) (y ◇ ((z ◇ x) ◇ w)) u).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_47201_to_50441 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_47201_to_50441
