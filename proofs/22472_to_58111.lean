-- Equation22472 → Equation58111
-- Recorded verdict: true
-- Premise: x = (y ◇ (x ◇ x)) ◇ ((z ◇ w) ◇ z)
-- Conclusion: x ◇ (y ◇ z) = ((w ◇ z) ◇ y) ◇ w
-- Original submission SHA-256: 4aed70855f1dcbd7a9ca20117327b8464e7367d1d6977b484fe13e1293c9483b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ (x ◇ x)) ◇ ((z ◇ w) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ z) = ((w ◇ z) ◇ y) ◇ w
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2:G), ((q2 ◇ (q1 ◇ q1)) ◇ q0) = q1:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => (q2 ◇ (q1 ◇ q1)) ◇ t) ((h q0 ((q0 ◇ q0) ◇ q0) q0 q0).symm)).symm).trans ((h q1 q2 ((q0 ◇ q0) ◇ q0) (q0 ◇ q0)).symm)
  have apc1 : forall (q3 q4 q5 q6:G), (q4 ◇ (q3 ◇ q3)) = ((q6 ◇ q3) ◇ q5):=by
    intro q3 q4 q5 q6
    exact (((congrArg (fun t => t ◇ q5) (congrArg (fun t => q6 ◇ t) (apc0 (q4 ◇ (q3 ◇ q3)) q3 q4))).symm).trans (apc0 q5 (q4 ◇ (q3 ◇ q3)) q6)).symm
  have apc8 : forall (q7 q8 q9 q10:G), (q9 ◇ (q8 ◇ q8)) = (q7 ◇ q10):=by
    intro q7 q8 q9 q10
    exact (((congrArg (fun t => t ◇ q10) (apc0 q8 q7 q7)).symm).trans ((apc1 q8 q9 q10 (q7 ◇ (q7 ◇ q7))).symm)).symm
  exact ((apc8 x (x ◇ (y ◇ z)) (((w ◇ z) ◇ y) ◇ w) (y ◇ z)).symm).trans (apc8 ((w ◇ z) ◇ y) (x ◇ (y ◇ z)) (((w ◇ z) ◇ y) ◇ w) w)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_22472_to_58111 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_22472_to_58111
