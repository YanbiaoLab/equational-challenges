-- Equation46607 → Equation47647
-- Recorded verdict: true
-- Premise: x * y = (z * z) * (z * (x * x))
-- Conclusion: x * y = (z * w) * ((u * z) * u)
-- Original submission SHA-256: a68a710939ba78da0e5d7fbb9d8ff85ba7a5bc2db6201dfa2642d3f2a53cb68e
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (z ◇ z) ◇ (z ◇ (x ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = (z ◇ w) ◇ ((u ◇ z) ◇ u)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (x y z:G), (x ◇ y) = (x ◇ x):=by
    intro x y z
    exact (h x y z).trans ((h x x z).symm)
  have apc1 : forall (q0 q1 q2:G), ((q1 ◇ q1) ◇ (q1 ◇ q1)) = (q0 ◇ q0):=by
    intro q0 q1 q2
    exact (((apc0 (q1 ◇ q1) (q1 ◇ (q0 ◇ q0)) q0).symm).trans ((h q0 q2 q1).symm)).trans (apc0 q0 q2 (q0 ◇ q2))
  have apc2 : forall (q3 q4 q5 q6:G), ((q5 ◇ q5) ◇ (q5 ◇ q5)) = ((q3 ◇ q3) ◇ q4):=by
    intro q3 q4 q5 q6
    exact ((congrArg (fun t => (q5 ◇ q5) ◇ t) (apc0 q5 (q6 ◇ q6) (q5 ◇ (q6 ◇ q6)))).symm).trans (((congrArg (fun t => (q5 ◇ q5) ◇ t) (congrArg (fun t => q5 ◇ t) (apc1 q6 q3 q6))).symm).trans ((h (q3 ◇ q3) q4 q5).symm))
  have apc4 : forall (q7 q8 q9 q10:G), (((q7 ◇ q7) ◇ q8) ◇ ((q7 ◇ q7) ◇ q8)) = (q9 ◇ q9):=by
    intro q7 q8 q9 q10
    exact ((apc0 ((q7 ◇ q7) ◇ q8) ((q10 ◇ q10) ◇ (q10 ◇ q10)) (((q7 ◇ q7) ◇ q8) ◇ ((q10 ◇ q10) ◇ (q10 ◇ q10)))).symm).trans (((congrArg (fun t => t ◇ ((q10 ◇ q10) ◇ (q10 ◇ q10))) (apc2 q7 q8 q10 q7)).symm).trans (apc1 q9 (q10 ◇ q10) q7))
  have apc11 : forall (q11 q12 q13:G), (q13 ◇ q13) = (q12 ◇ q11):=by
    intro q11 q12 q13
    exact ((h q12 q11 (q12 ◇ q12)).trans (apc4 q12 (q12 ◇ q12) q13 q11)).symm
  exact ((apc11 y x (x ◇ y)).symm).trans (apc11 ((u ◇ z) ◇ u) (z ◇ w) (x ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_46607_to_47647 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_46607_to_47647
