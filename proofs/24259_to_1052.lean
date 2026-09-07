-- Equation24259 → Equation1052
-- Recorded verdict: true
-- Premise: x = ((y ◇ x) ◇ y) ◇ ((z ◇ z) ◇ z)
-- Conclusion: x = x ◇ ((y ◇ (y ◇ z)) ◇ y)
-- Original submission SHA-256: b1cd9634f993abdba0635df6a98891736cf6832700b9d4f6f9c000c6ee0bccc4
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ x) ◇ y) ◇ ((z ◇ z) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = x ◇ ((y ◇ (y ◇ z)) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1:G), (q0 ◇ ((q1 ◇ q1) ◇ q1)) = (q0 ◇ q0):=by
    intro q0 q1
    exact ((congrArg (fun t => t ◇ ((q1 ◇ q1) ◇ q1)) ((h q0 (q0 ◇ q0) q0).symm)).symm).trans ((h (q0 ◇ q0) ((q0 ◇ q0) ◇ q0) q1).symm)
  have apc1 : forall (q2 q3:G), (q3 ◇ (q2 ◇ q2)) = (q3 ◇ q3):=by
    intro q2 q3
    exact ((congrArg (fun t => q3 ◇ t) (apc0 q2 q2)).symm).trans (((congrArg (fun t => q3 ◇ t) (congrArg (fun t => t ◇ ((q2 ◇ q2) ◇ q2)) ((h q2 q2 q2).symm))).symm).trans (apc0 q3 ((q2 ◇ q2) ◇ q2)))
  have apc2 : forall (q4 q5:G), (q5 ◇ q5) = (q5 ◇ q4):=by
    intro q4 q5
    exact (((congrArg (fun t => q5 ◇ t) ((h q4 q4 q4).symm)).symm).trans (apc1 ((q4 ◇ q4) ◇ q4) q5)).symm
  have apc4 : forall (q6 q7 q8:G), (q8 ◇ (q7 ◇ q6)) = (q8 ◇ q8):=by
    intro q6 q7 q8
    exact ((congrArg (fun t => q8 ◇ t) (apc2 q6 q7)).symm).trans (apc1 q7 q8)
  have apc5 : forall (x y z:G), (((y ◇ x) ◇ y) ◇ ((y ◇ x) ◇ y)) = (((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)):=by
    intro x y z
    exact ((apc4 z (z ◇ z) ((y ◇ x) ◇ y)).symm).trans (((h x y z).symm).trans (h x x x))
  have apc6 : forall (q9 q10:G), (((q9 ◇ q9) ◇ q9) ◇ ((q9 ◇ q9) ◇ q9)) = q9:=by
    intro q9 q10
    exact ((apc5 q9 q10 (((q10 ◇ q9) ◇ q10) ◇ ((q10 ◇ q9) ◇ q10))).symm).trans (((apc0 ((q10 ◇ q9) ◇ q10) q9).symm).trans ((h q9 q10 q9).symm))
  have apc7 : forall (x y z q9 q10:G), (((y ◇ x) ◇ y) ◇ ((y ◇ x) ◇ y)) = x:=by
    intro x y z q9 q10
    exact (apc5 x y z).trans (apc6 x (((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)))
  have apc8 : forall (q11 q12 q13:G), (q12 ◇ q11) = q13:=by
    intro q11 q12 q13
    exact ((((congrArg (fun t => ((q13 ◇ q13) ◇ q13) ◇ t) (congrArg (fun t => t ◇ q13) (apc4 q11 q12 q13))).trans (apc7 q13 q13 (((q13 ◇ q13) ◇ q13) ◇ ((q13 ◇ q13) ◇ q13)) (((q13 ◇ q13) ◇ q13) ◇ ((q13 ◇ q13) ◇ q13)) (((q13 ◇ q13) ◇ q13) ◇ ((q13 ◇ q13) ◇ q13)))).symm).trans (((congrArg (fun t => t ◇ ((q13 ◇ (q12 ◇ q11)) ◇ q13)) (congrArg (fun t => t ◇ q13) (apc4 q11 q12 q13))).symm).trans (apc7 (q12 ◇ q11) q13 q11 q11 q11))).symm
  exact ((apc8 x y x).symm).trans ((apc8 ((y ◇ (y ◇ z)) ◇ y) x (y ◇ x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_24259_to_1052 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_24259_to_1052
