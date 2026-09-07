-- Equation49299 → Equation42851
-- Recorded verdict: true
-- Premise: x * y = ((z * w) * x) * (w * w)
-- Conclusion: x * y = y * (z * ((y * x) * x))
-- Original submission SHA-256: 08388b874deaf65153c95580e33ca9f1d4252bd94a8bd196ceaa8ee24e981684
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ w) ◇ x) ◇ (w ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ (z ◇ ((y ◇ x) ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z w:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w
    exact (h x y z w).trans ((h x x z w).symm)
  have apc1 : forall (q0 q1 q2 q3:G), (((q2 ◇ q0) ◇ q1) ◇ (q0 ◇ q0)) = (q1 ◇ q1):=by
    intro q0 q1 q2 q3
    exact (((congrArg (fun t => ((q2 ◇ q0) ◇ q1) ◇ t) (apc0 q0 q0 q0 q0)).symm).trans ((h q1 q3 q2 q0).symm)).trans (apc0 q1 q3 (q1 ◇ q3) (q1 ◇ q3))
  have apc2 : forall (q4 q5 q6:G), ((q6 ◇ q4) ◇ (q6 ◇ q4)) = (q5 ◇ q5):=by
    intro q4 q5 q6
    exact ((apc1 q4 (q6 ◇ q4) q6 (((q6 ◇ q4) ◇ (q6 ◇ q4)) ◇ (q4 ◇ q4))).symm).trans (((congrArg (fun t => t ◇ (q4 ◇ q4)) (apc0 (q6 ◇ q4) q5 q4 q4)).symm).trans (apc1 q4 q5 q6 q4))
  have apc3 : forall (q4 q5 q6:G), (q5 ◇ q5) = (q4 ◇ q4):=by
    intro q4 q5 q6
    exact ((apc2 q4 q5 q6).symm).trans (apc2 q4 q4 q6)
  have apc4 : forall (q7 q8 q9:G), ((q8 ◇ q8) ◇ (q7 ◇ q7)) = (q9 ◇ q9):=by
    intro q7 q8 q9
    exact ((congrArg (fun t => (q8 ◇ q8) ◇ t) (apc3 q7 q8 q7)).symm).trans (apc2 q8 q9 q8)
  have apc8 : forall (q10 q11 q12 q13:G), ((q13 ◇ q11) ◇ q12) = (q10 ◇ q10):=by
    intro q10 q11 q12 q13
    exact (((apc4 q11 (q13 ◇ q11) q10).symm).trans ((h (q13 ◇ q11) q12 q13 q11).symm)).symm
  have apc10 : forall (q14 q15 q16:G), (q16 ◇ q14) = (q15 ◇ q15):=by
    intro q14 q15 q16
    exact (h q16 q14 q14 q14).trans (apc8 q15 q16 (q14 ◇ q14) (q14 ◇ q14))
  exact (apc10 y (x ◇ y) x).trans ((apc10 (z ◇ ((y ◇ x) ◇ x)) (x ◇ y) y).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_49299_to_42851 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_49299_to_42851
