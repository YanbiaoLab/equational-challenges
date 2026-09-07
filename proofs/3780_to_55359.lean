-- Equation3780 → Equation55359
-- Recorded verdict: true
-- Premise: x * y = (y * z) * (w * x)
-- Conclusion: x * (y * z) = z * ((x * w) * u)
-- Original submission SHA-256: f485b35a064809bcd98b036bcfef401f9a0a1d0c17af268443f60f6cca8c1aa4
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (y ◇ z) ◇ (w ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ (y ◇ z) = z ◇ ((x ◇ w) ◇ u)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1 q2 q3 q4:G), ((q0 ◇ q1) ◇ (q3 ◇ q4)) = (q4 ◇ (q1 ◇ q2)):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => t ◇ (q3 ◇ q4)) ((h q0 q1 q2 q0).symm)).symm).trans ((h q4 (q1 ◇ q2) (q0 ◇ q0) q3).symm)
  have apc1 : forall (q5 q6 q7 q8:G), (q6 ◇ (q8 ◇ q5)) = (q6 ◇ q7):=by
    intro q5 q6 q7 q8
    exact ((apc0 q7 q8 q5 q5 q6).symm).trans ((h q6 q7 q8 q5).symm)
  have apc2 : forall (q5 q6 q7 q8:G), (q6 ◇ q7) = (q6 ◇ q5):=by
    intro q5 q6 q7 q8
    exact ((apc1 q5 q6 q7 q8).symm).trans (apc1 q5 q6 q5 q8)
  have apc3 : forall (q5 q6 q7 q8:G), (q6 ◇ q6) = (q6 ◇ q5):=by
    intro q5 q6 q7 q8
    exact (((apc2 q5 q6 q7 q8).symm).trans (apc2 q6 q6 q7 q8)).symm
  have apc4 : forall (q9 q10 q11 q12:G), ((q11 ◇ q12) ◇ q9) = (q10 ◇ q11):=by
    intro q9 q10 q11 q12
    exact ((apc1 q10 (q11 ◇ q12) q9 q9).symm).trans ((h q10 q11 q12 q9).symm)
  have apc6 : forall (q9 q10 q11 q12:G), (q10 ◇ q11) = (q9 ◇ q11):=by
    intro q9 q10 q11 q12
    exact ((apc4 q9 q10 q11 q12).symm).trans (apc4 q9 q9 q11 q12)
  have apc8 : forall (q13 q14 q15:G), (q15 ◇ q14) = (q13 ◇ q15):=by
    intro q13 q14 q15
    exact (((apc6 q13 q15 q15 q13).symm).trans (apc3 q14 q15 q13 q13)).symm
  exact (apc8 ((x ◇ w) ◇ u) (y ◇ z) x).trans (apc8 z x ((x ◇ w) ◇ u))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_3780_to_55359 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_3780_to_55359
