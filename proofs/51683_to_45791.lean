-- Equation51683 → Equation45791
-- Recorded verdict: true
-- Premise: x * y = ((z * x) * (x * x)) * z
-- Conclusion: x * y = z * (((w * x) * w) * w)
-- Original submission SHA-256: d7670a5ebde511ae3b013a7368b564b183e04dba97273121d6e32cb1348c88ad
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((z ◇ x) ◇ (x ◇ x)) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ (((w ◇ x) ◇ w) ◇ w)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z:G), (x ◇ y) = (x ◇ x):=by
    intro x y z
    exact (h x y z).trans ((h x x z).symm)
  have apc1 : forall (q0 q1 q2:G), ((q0 ◇ q0) ◇ (q0 ◇ q0)) = ((q0 ◇ q0) ◇ q1):=by
    intro q0 q1 q2
    exact (((congrArg (fun t => t ◇ (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ q0)) (apc0 q0 q2 (q0 ◇ q2))).trans (apc0 (q0 ◇ q0) (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ q0) ((q0 ◇ q0) ◇ (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ q0)))).symm).trans (((congrArg (fun t => t ◇ (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ q0)) ((h q0 q2 ((q0 ◇ q0) ◇ (q0 ◇ q0))).symm)).symm).trans ((h (q0 ◇ q0) q1 (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ q0)).symm))
  have apc2 : forall (q3 q4 q5:G), (((q4 ◇ q4) ◇ q3) ◇ q4) = (q4 ◇ q4):=by
    intro q3 q4 q5
    exact (((congrArg (fun t => t ◇ q4) (apc1 q4 q3 q3)).symm).trans ((h q4 q5 q4).symm)).trans (apc0 q4 q5 (q4 ◇ q5))
  have apc3 : forall (q6 q7 q8:G), (q7 ◇ q7) = (q6 ◇ q6):=by
    intro q6 q7 q8
    exact ((((apc2 q8 q6 q8).symm).trans (h ((q6 ◇ q6) ◇ q8) q6 q7)).trans (((congrArg (fun t => t ◇ q7) (congrArg (fun t => t ◇ (((q6 ◇ q6) ◇ q8) ◇ ((q6 ◇ q6) ◇ q8))) (apc0 q7 ((q6 ◇ q6) ◇ q8) (q7 ◇ ((q6 ◇ q6) ◇ q8))))).trans (congrArg (fun t => t ◇ q7) (apc0 (q7 ◇ q7) (((q6 ◇ q6) ◇ q8) ◇ ((q6 ◇ q6) ◇ q8)) ((q7 ◇ q7) ◇ (((q6 ◇ q6) ◇ q8) ◇ ((q6 ◇ q6) ◇ q8)))))).trans (apc2 (q7 ◇ q7) q7 (((q7 ◇ q7) ◇ (q7 ◇ q7)) ◇ q7)))).symm
  have apc10 : forall (q9 q10:G), (((q10 ◇ q10) ◇ (q10 ◇ q10)) ◇ ((q10 ◇ q10) ◇ (q10 ◇ q10))) = (q10 ◇ q9):=by
    intro q9 q10
    exact ((h q10 q9 q10).trans ((apc1 (q10 ◇ q10) q10 q9).symm)).symm
  have apc12 : forall (q11 q12 q13:G), (q13 ◇ q13) = (q12 ◇ q11):=by
    intro q11 q12 q13
    exact (((apc10 q11 q12).symm).trans (apc3 q13 ((q12 ◇ q12) ◇ (q12 ◇ q12)) q11)).symm
  exact ((apc12 y x (x ◇ y)).symm).trans (apc12 (((w ◇ x) ◇ w) ◇ w) z (x ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_51683_to_45791 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_51683_to_45791
