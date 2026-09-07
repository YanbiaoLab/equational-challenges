-- Equation43119 → Equation45966
-- Recorded verdict: true
-- Premise: x * y = z * (z * ((w * x) * w))
-- Conclusion: x * x = (y * x) * (x * (x * x))
-- Original submission SHA-256: 3a3c33cce5a441141518482ebed0b2df427e6359e06f719a592b970284d6de57
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ (z ◇ ((w ◇ x) ◇ w))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ x = (y ◇ x) ◇ (x ◇ (x ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (x y z w:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w
    exact (h x y z w).trans ((h x x z w).symm)
  have apc1 : forall (q0 q1 q2:G), (q1 ◇ q1) = (q0 ◇ q0):=by
    intro q0 q1 q2
    exact (((apc0 q1 (q1 ◇ ((q0 ◇ q0) ◇ q0)) q0 q0).symm).trans ((h q0 q2 q1 q0).symm)).trans (apc0 q0 q2 (q0 ◇ q2) (q0 ◇ q2))
  have apc2 : forall (q3 q4 q5 q6:G), (((q4 ◇ q4) ◇ q4) ◇ (q3 ◇ q3)) = (q5 ◇ q5):=by
    intro q3 q4 q5 q6
    exact ((congrArg (fun t => t ◇ (q3 ◇ q3)) (congrArg (fun t => t ◇ q4) (apc0 q4 q5 (q4 ◇ q5) (q4 ◇ q5)))).symm).trans ((((congrArg (fun t => ((q4 ◇ q5) ◇ q4) ◇ t) (apc1 q3 ((q4 ◇ q5) ◇ q4) q3)).symm).trans ((h q5 q6 ((q4 ◇ q5) ◇ q4) q4).symm)).trans (apc0 q5 q6 (q5 ◇ q6) (q5 ◇ q6)))
  have apc7 : forall (q7 q8 q9:G), (q9 ◇ q9) = (q8 ◇ q7):=by
    intro q7 q8 q9
    exact ((h q8 q7 ((q8 ◇ q8) ◇ q8) q8).trans (apc2 ((q8 ◇ q8) ◇ q8) q8 q9 q7)).symm
  exact (apc7 (x ◇ x) (x ◇ x) x).trans (apc7 (x ◇ (x ◇ x)) (y ◇ x) (x ◇ x))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_43119_to_45966 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_43119_to_45966
