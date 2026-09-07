-- Equation48407 → Equation62469
-- Recorded verdict: true
-- Premise: x * y = (z * (w * x)) * (x * w)
-- Conclusion: (x * y) * z = ((w * y) * y) * z
-- Original submission SHA-256: 5341f7c37449e01b4403b0c47558446212c859225a73867d9b29d69c6a6663a4
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ (w ◇ x)) ◇ (x ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ z = ((w ◇ y) ◇ y) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w
    exact (h x y z w).trans ((h x x z w).symm)
  have apc1 : forall (q0 q1 q2 q3:G), ((q1 ◇ q0) ◇ (q1 ◇ q0)) = (q2 ◇ q2):=by
    intro q0 q1 q2 q3
    exact ((apc0 (q1 ◇ q0) (q2 ◇ q1) ((q1 ◇ q0) ◇ (q2 ◇ q1)) ((q1 ◇ q0) ◇ (q2 ◇ q1))).symm).trans ((((congrArg (fun t => t ◇ (q2 ◇ q1)) ((h q1 q0 q0 q2).symm)).symm).trans ((h q2 q3 (q0 ◇ (q2 ◇ q1)) q1).symm)).trans (apc0 q2 q3 (q2 ◇ q3) (q2 ◇ q3)))
  have apc2 : forall (q4 q5 q6 q7 q8:G), ((q7 ◇ q7) ◇ (q7 ◇ q7)) = ((q5 ◇ q4) ◇ q6):=by
    intro q4 q5 q6 q7 q8
    exact (((congrArg (fun t => t ◇ ((q5 ◇ q4) ◇ (q5 ◇ q4))) (apc0 q7 (q8 ◇ q8) (q7 ◇ (q8 ◇ q8)) (q7 ◇ (q8 ◇ q8)))).trans (apc0 (q7 ◇ q7) ((q5 ◇ q4) ◇ (q5 ◇ q4)) ((q7 ◇ q7) ◇ ((q5 ◇ q4) ◇ (q5 ◇ q4))) ((q7 ◇ q7) ◇ ((q5 ◇ q4) ◇ (q5 ◇ q4))))).symm).trans (((congrArg (fun t => t ◇ ((q5 ◇ q4) ◇ (q5 ◇ q4))) (congrArg (fun t => q7 ◇ t) (apc1 q4 q5 q8 q4))).symm).trans ((h (q5 ◇ q4) q6 q7 (q5 ◇ q4)).symm))
  exact ((apc2 y x z ((x ◇ y) ◇ z) ((x ◇ y) ◇ z)).symm).trans (apc2 y (w ◇ y) z ((x ◇ y) ◇ z) ((x ◇ y) ◇ z))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_48407_to_62469 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_48407_to_62469
