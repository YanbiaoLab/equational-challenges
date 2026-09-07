-- Equation42020 → Equation42091
-- Recorded verdict: true
-- Premise: x * y = y * (z * (w * (z * z)))
-- Conclusion: x * y = z * (x * (w * (y * y)))
-- Original submission SHA-256: 159e91f694e7246a57e2a6e34ea87b6721e1e388455e7a751587d7bbea786f5c
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = y ◇ (z ◇ (w ◇ (z ◇ z)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ (x ◇ (w ◇ (y ◇ y)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3:G), (q3 ◇ (q0 ◇ (q1 ◇ q1))) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => q3 ◇ t) ((h q0 (q1 ◇ q1) q1 (q1 ◇ q1)).symm)).symm).trans ((h q2 q3 (q1 ◇ q1) q1).symm)
  have apc1 : forall (x y z w:G), (y ◇ y) = (x ◇ y):=by
    intro x y z w
    exact ((h x y z w).trans ((h y y z w).symm)).symm
  have apc4 : forall (q4 q5 q6 q7 q8:G), (q8 ◇ (q5 ◇ (q4 ◇ q6))) = (q7 ◇ q8):=by
    intro q4 q5 q6 q7 q8
    exact ((congrArg (fun t => q8 ◇ t) (congrArg (fun t => q5 ◇ t) (apc1 q4 q6 q4 q4))).symm).trans (apc0 q5 q6 q7 q8)
  have apc5 : forall (q5 q6 q8:G), (q8 ◇ (q5 ◇ (q6 ◇ q6))) = (q8 ◇ q8):=by
    intro q5 q6 q8
    exact ((apc1 q5 q8 q5 q5).trans ((apc0 q5 q6 q5 q8).symm)).symm
  have apc6 : forall (q9 q10 q11 q12 q13 q14:G), (q12 ◇ (q10 ◇ (q9 ◇ q11))) = (q12 ◇ (q13 ◇ q13)):=by
    intro q9 q10 q11 q12 q13 q14
    exact ((apc4 q9 q10 q11 q9 q12).trans (h q9 q12 q13 q14)).trans (congrArg (fun t => q12 ◇ t) (apc5 q14 q13 q13))
  have apc9 : forall (q15 q16 q17 q18 q19 q20 q21:G), (q18 ◇ (q16 ◇ (q15 ◇ q17))) = (q18 ◇ q18):=by
    intro q15 q16 q17 q18 q19 q20 q21
    exact ((((congrArg (fun t => q18 ◇ t) (congrArg (fun t => q19 ◇ t) (apc5 q20 q21 q21))).trans (apc5 q19 q21 q18)).symm).trans (((congrArg (fun t => q18 ◇ t) ((h q19 (q21 ◇ (q20 ◇ (q21 ◇ q21))) q21 q20).symm)).symm).trans ((apc6 q15 q16 q17 q18 (q21 ◇ (q20 ◇ (q21 ◇ q21))) q20).symm))).symm
  have apc10 : forall (q0 q2 q3:G), (q2 ◇ q3) = (q0 ◇ q3):=by
    intro q0 q2 q3
    exact ((h q0 q3 q0 q0).trans ((h q2 q3 q0 q0).symm)).symm
  have apc12 : forall (q22 q23 q24 q25 q26:G), (q22 ◇ (q25 ◇ q25)) = (q23 ◇ q24):=by
    intro q22 q23 q24 q25 q26
    exact ((congrArg (fun t => q22 ◇ t) (apc9 q25 q26 q25 q25 (q25 ◇ (q26 ◇ (q25 ◇ q25))) (q25 ◇ (q26 ◇ (q25 ◇ q25))) (q25 ◇ (q26 ◇ (q25 ◇ q25))))).symm).trans (((apc10 q22 q24 (q25 ◇ (q26 ◇ (q25 ◇ q25)))).symm).trans ((h q23 q24 q25 q26).symm))
  exact ((apc12 (z ◇ (x ◇ (w ◇ (y ◇ y)))) x y (x ◇ y) (x ◇ y)).symm).trans (apc12 (z ◇ (x ◇ (w ◇ (y ◇ y)))) z (x ◇ (w ◇ (y ◇ y))) (x ◇ y) (x ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_42020_to_42091 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_42020_to_42091
