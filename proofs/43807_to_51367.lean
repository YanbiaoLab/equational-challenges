-- Equation43807 → Equation51367
-- Recorded verdict: true
-- Premise: x * y = z * ((x * y) * (x * z))
-- Conclusion: x * x = ((y * z) * (w * z)) * u
-- Original submission SHA-256: a0636556145f4a2656b33d53127fca36651b05c1befd67c0c09dd51a9f9471d6
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = z ◇ ((x ◇ y) ◇ (x ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ x = ((y ◇ z) ◇ (w ◇ z)) ◇ u
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (x y z:G), (z ◇ ((x ◇ y) ◇ (x ◇ z))) = (x ◇ ((x ◇ y) ◇ (x ◇ x))):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have apc1 : forall (x y z:G), (x ◇ ((x ◇ y) ◇ (x ◇ x))) = (x ◇ y):=by
    intro x y z
    exact ((h x y x).trans (apc0 x y x)).symm
  have apc2 : forall (q0 q1 q2 q3:G), (q3 ◇ ((q0 ◇ q1) ◇ (q2 ◇ q3))) = (q2 ◇ ((q0 ◇ q1) ◇ (q0 ◇ q2))):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => q3 ◇ t) (congrArg (fun t => t ◇ (q2 ◇ q3)) ((h q0 q1 q2).symm))).symm).trans ((h q2 ((q0 ◇ q1) ◇ (q0 ◇ q2)) q3).symm)
  have apc3 : forall (q4 q5 q6 q7:G), ((q4 ◇ (q6 ◇ q7)) ◇ (q4 ◇ q5)) = (q6 ◇ q7):=by
    intro q4 q5 q6 q7
    exact (((congrArg (fun t => (q4 ◇ (q6 ◇ q7)) ◇ t) ((h q4 q5 (q6 ◇ q7)).symm)).symm).trans (apc2 q6 q7 (q4 ◇ q5) (q4 ◇ (q6 ◇ q7)))).trans ((apc2 q6 q7 q6 (q4 ◇ q5)).trans (apc1 q6 q7 (q6 ◇ ((q6 ◇ q7) ◇ (q6 ◇ q6)))))
  have apc4 : forall (q8 q9 q10 q11:G), (q10 ◇ q11) = (q8 ◇ q9):=by
    intro q8 q9 q10 q11
    exact (((apc3 (q10 ◇ q11) (q10 ◇ ((q10 ◇ q11) ◇ (q8 ◇ q9))) q8 q9).symm).trans ((h q10 q11 ((q10 ◇ q11) ◇ (q8 ◇ q9))).symm)).symm
  have apc5 : forall (q8 q9 q10 q11:G), (q10 ◇ q10) = (q8 ◇ q9):=by
    intro q8 q9 q10 q11
    exact (((apc4 q8 q9 q10 q8).symm).trans (apc4 q10 q10 q10 q8)).symm
  exact (apc5 (x ◇ x) (x ◇ x) x (x ◇ x)).trans (apc5 ((y ◇ z) ◇ (w ◇ z)) u (x ◇ x) (x ◇ x))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_43807_to_51367 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_43807_to_51367
