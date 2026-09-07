-- Equation42827 → Equation46355
-- Recorded verdict: true
-- Premise: x * y = y * (y * ((z * z) * z))
-- Conclusion: x * y = (y * z) * (x * (w * y))
-- Original submission SHA-256: 4d654b22d22f455d2af88ee9b80902943d7374dfef171c096417d2fc911c2044
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ (y ◇ ((z ◇ z) ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (y ◇ z) ◇ (x ◇ (w ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z:G), (y ◇ y) = (x ◇ y):=by
    intro x y z
    exact ((h x y z).trans ((h y y z).symm)).symm
  have apc1 : forall (q0 q1 q2:G), (q1 ◇ (q1 ◇ (q2 ◇ q2))) = (q0 ◇ q1):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q1 ◇ t) (congrArg (fun t => q1 ◇ t) ((apc0 (q2 ◇ q2) q2 q0).symm))).symm).trans ((h q0 q1 q2).symm)
  have apc2 : forall (q3 q4 q5 q6:G), (q5 ◇ (q5 ◇ (q3 ◇ q6))) = (q4 ◇ q5):=by
    intro q3 q4 q5 q6
    exact ((congrArg (fun t => q5 ◇ t) (congrArg (fun t => q5 ◇ t) (apc0 q3 q6 q3))).symm).trans (apc1 q4 q5 q6)
  have apc4 : forall (q7 q8 q9:G), (q9 ◇ (q9 ◇ (q7 ◇ q8))) = (q9 ◇ q9):=by
    intro q7 q8 q9
    exact (apc2 q7 q7 q9 q8).trans ((apc0 q7 q9 q7).symm)
  have apc6 : forall (q10 q11 q12:G), ((q12 ◇ (q11 ◇ q11)) ◇ (q12 ◇ (q11 ◇ q11))) = (q10 ◇ q12):=by
    intro q10 q11 q12
    exact (((apc1 q10 q12 q11).symm).trans ((apc0 q12 (q12 ◇ (q11 ◇ q11)) q10).symm)).symm
  have apc7 : forall (q13 q14 q15 q16:G), (q16 ◇ (q15 ◇ (q14 ◇ q14))) = (q13 ◇ q15):=by
    intro q13 q14 q15 q16
    exact (((apc6 q13 q14 q15).symm).trans (apc0 q16 (q15 ◇ (q14 ◇ q14)) q13)).symm
  have apc12 : forall (q17 q18 q19 q20:G), (q18 ◇ (q19 ◇ (q17 ◇ q17))) = (q19 ◇ q19):=by
    intro q17 q18 q19 q20
    exact ((apc7 q17 q17 q19 q18).trans (h q17 q19 q20)).trans (apc4 (q20 ◇ q20) q20 q19)
  have apc13 : forall (q21 q22 q23:G), ((q21 ◇ q21) ◇ (q21 ◇ q21)) = (q22 ◇ q23):=by
    intro q21 q22 q23
    exact (((congrArg (fun t => q23 ◇ t) (apc12 q21 ((q21 ◇ q21) ◇ (q21 ◇ q21)) (q21 ◇ q21) (((q21 ◇ q21) ◇ (q21 ◇ q21)) ◇ ((q21 ◇ q21) ◇ (q21 ◇ q21))))).trans (apc12 q21 q23 (q21 ◇ q21) (q23 ◇ ((q21 ◇ q21) ◇ (q21 ◇ q21))))).symm).trans (((congrArg (fun t => q23 ◇ t) (apc12 q21 q23 ((q21 ◇ q21) ◇ (q21 ◇ q21)) q21)).symm).trans ((h q22 q23 (q21 ◇ q21)).symm))
  exact ((apc13 (x ◇ y) x y).symm).trans (apc13 (x ◇ y) (y ◇ z) (x ◇ (w ◇ y)))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_42827_to_46355 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_42827_to_46355
