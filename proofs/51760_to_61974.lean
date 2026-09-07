-- Equation51760 → Equation61974
-- Recorded verdict: true
-- Premise: x * y = ((z * y) * (x * x)) * z
-- Conclusion: (x * y) * x = ((y * z) * w) * z
-- Original submission SHA-256: 4a885900e861f0b280cc918eaa87940284f66fb524dd422a05861acc6a131df6
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((z ◇ y) ◇ (x ◇ x)) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ x = ((y ◇ z) ◇ w) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2:G), ((q0 ◇ q1) ◇ ((q2 ◇ q2) ◇ q1)) = (q2 ◇ (q0 ◇ q0)):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ ((q2 ◇ q2) ◇ q1)) ((h q0 q1 (q2 ◇ q2)).symm)).symm).trans ((h q2 (q0 ◇ q0) ((q2 ◇ q2) ◇ q1)).symm)
  have apc1 : forall (q3 q4:G), ((q3 ◇ (q4 ◇ q4)) ◇ q4) = ((q3 ◇ q3) ◇ (q3 ◇ q3)):=by
    intro q3 q4
    exact ((congrArg (fun t => t ◇ q4) (apc0 q4 (q3 ◇ q3) q3)).symm).trans ((h (q3 ◇ q3) (q3 ◇ q3) q4).symm)
  have apc2 : forall (q5 q6:G), (((q6 ◇ q5) ◇ (q6 ◇ q5)) ◇ ((q6 ◇ q5) ◇ (q6 ◇ q5))) = (q6 ◇ q5):=by
    intro q5 q6
    exact ((apc1 (q6 ◇ q5) q6).symm).trans ((h q6 q5 q6).symm)
  have apc4 : forall (q7 q8 q9:G), ((q9 ◇ q9) ◇ (q9 ◇ q9)) = ((q8 ◇ q7) ◇ (q9 ◇ q9)):=by
    intro q7 q8 q9
    exact ((apc1 q9 (q8 ◇ q7)).symm).trans (((congrArg (fun t => (q9 ◇ ((q8 ◇ q7) ◇ (q8 ◇ q7))) ◇ t) (apc2 q7 q8)).symm).trans (apc0 q9 ((q8 ◇ q7) ◇ (q8 ◇ q7)) (q8 ◇ q7)))
  have apc8 : forall (q10 q11 q12:G), ((q10 ◇ q10) ◇ (q10 ◇ q10)) = (q11 ◇ q12):=by
    intro q10 q11 q12
    exact (apc4 (q11 ◇ q11) ((q10 ◇ q10) ◇ q12) q10).trans ((h q11 q12 (q10 ◇ q10)).symm)
  exact ((apc8 ((x ◇ y) ◇ x) (x ◇ y) x).symm).trans (apc8 ((x ◇ y) ◇ x) ((y ◇ z) ◇ w) z)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_51760_to_61974 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_51760_to_61974
