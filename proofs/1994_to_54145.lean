-- Equation1994 → Equation54145
-- Recorded verdict: true
-- Premise: x = (y ◇ (z ◇ z)) ◇ (x ◇ z)
-- Conclusion: x ◇ (y ◇ x) = z ◇ (w ◇ (z ◇ x))
-- Original submission SHA-256: 0746321a74311f74f6677ab448b3cecfde4dd8604ab4a9a70dd9e0b40231354f
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (z ◇ z)) ◇ (x ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ x) = z ◇ (w ◇ (z ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1:G), (q1 ◇ (q0 ◇ q1)) = q0:=by
    intro q0 q1
    exact ((congrArg (fun t => t ◇ (q0 ◇ q1)) ((h q1 q0 q1).symm)).symm).trans ((h q0 (q0 ◇ (q1 ◇ q1)) q1).symm)
  have apc1 : forall (q2 q3 q4:G), (q3 ◇ (q4 ◇ q4)) = ((q2 ◇ q4) ◇ q2):=by
    intro q2 q3 q4
    exact (((congrArg (fun t => (q2 ◇ q4) ◇ t) ((h q2 q3 q4).symm)).symm).trans (apc0 (q3 ◇ (q4 ◇ q4)) (q2 ◇ q4))).symm
  have apc2 : forall (q2 q3 q4:G), (q3 ◇ (q4 ◇ q4)) = (q2 ◇ (q4 ◇ q4)):=by
    intro q2 q3 q4
    exact (apc1 q2 q3 q4).trans ((apc1 q2 q2 q4).symm)
  have apc3 : forall (q5 q6 q7:G), (q7 ◇ (q5 ◇ (q6 ◇ q6))) = (q7 ◇ q6):=by
    intro q5 q6 q7
    exact ((congrArg (fun t => q7 ◇ t) ((apc1 q7 q5 q6).symm)).symm).trans (apc0 (q7 ◇ q6) q7)
  have apc4 : forall (q8 q9 q10 q11:G), (q10 ◇ (q11 ◇ q11)) = (q8 ◇ (q9 ◇ q9)):=by
    intro q8 q9 q10 q11
    exact (((apc2 q8 ((q9 ◇ q9) ◇ q11) q9).symm).trans ((apc1 (q9 ◇ q9) q10 q11).symm)).symm
  have apc8 : forall (q12 q13 q14 q15 q16:G), (q13 ◇ (q14 ◇ q14)) = (q15 ◇ q12):=by
    intro q12 q13 q14 q15 q16
    exact (((apc3 q16 q12 q15).symm).trans (((congrArg (fun t => q15 ◇ t) (apc2 q16 (q12 ◇ q12) q12)).symm).trans (apc4 q13 q14 q15 (q12 ◇ q12)))).symm
  exact ((apc8 (y ◇ x) (z ◇ (w ◇ (z ◇ x))) (x ◇ (y ◇ x)) x (x ◇ (y ◇ x))).symm).trans (apc8 (w ◇ (z ◇ x)) (z ◇ (w ◇ (z ◇ x))) (x ◇ (y ◇ x)) z (x ◇ (y ◇ x)))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_1994_to_54145 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_1994_to_54145
