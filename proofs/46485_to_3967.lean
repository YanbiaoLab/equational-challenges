-- Equation46485 → Equation3967
-- Recorded verdict: true
-- Premise: x * y = (z * x) * (w * (w * x))
-- Conclusion: x * y = (y * (y * z)) * x
-- Original submission SHA-256: 5b7622809107381d784d163af781b5febc683eca01261bd73b401a227c9b39fb
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ x) ◇ (w ◇ (w ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (y ◇ (y ◇ z)) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z w:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w
    exact (h x y z w).trans ((h x x z w).symm)
  have apc1 : forall (q0 q1 q2:G), ((q1 ◇ q0) ◇ (q1 ◇ q0)) = (q0 ◇ q0):=by
    intro q0 q1 q2
    exact (((apc0 (q1 ◇ q0) (q0 ◇ (q0 ◇ q0)) q0 q0).symm).trans ((h q0 q2 q1 q0).symm)).trans (apc0 q0 q2 (q0 ◇ q2) (q0 ◇ q2))
  have apc2 : forall (q3 q4 q5 q6:G), ((q4 ◇ q3) ◇ q5) = (q3 ◇ q3):=by
    intro q3 q4 q5 q6
    exact ((((((congrArg (fun t => (q3 ◇ q3) ◇ t) (congrArg (fun t => q6 ◇ t) (apc0 q6 (q4 ◇ q3) (q6 ◇ (q4 ◇ q3)) (q6 ◇ (q4 ◇ q3))))).trans (congrArg (fun t => (q3 ◇ q3) ◇ t) (apc0 q6 (q6 ◇ q6) (q6 ◇ (q6 ◇ q6)) (q6 ◇ (q6 ◇ q6))))).trans (apc0 (q3 ◇ q3) (q6 ◇ q6) ((q3 ◇ q3) ◇ (q6 ◇ q6)) ((q3 ◇ q3) ◇ (q6 ◇ q6)))).trans (apc1 q3 q3 ((q3 ◇ q3) ◇ (q3 ◇ q3)))).symm).trans (((congrArg (fun t => t ◇ (q6 ◇ (q6 ◇ (q4 ◇ q3)))) (apc1 q3 q4 q3)).symm).trans ((h (q4 ◇ q3) q5 (q4 ◇ q3) q6).symm))).symm
  have apc3 : forall (q3 q7 q4 q5:G), (q7 ◇ q7) = (q3 ◇ q3):=by
    intro q3 q7 q4 q5
    exact ((((congrArg (fun t => t ◇ ((q4 ◇ q3) ◇ (q3 ◇ q3))) (apc0 q7 (q4 ◇ q3) (q7 ◇ (q4 ◇ q3)) (q7 ◇ (q4 ◇ q3)))).trans (congrArg (fun t => (q7 ◇ q7) ◇ t) (apc2 q3 q4 (q3 ◇ q3) ((q4 ◇ q3) ◇ (q3 ◇ q3))))).trans (apc2 q7 q7 (q3 ◇ q3) ((q7 ◇ q7) ◇ (q3 ◇ q3)))).symm).trans ((((congrArg (fun t => (q7 ◇ (q4 ◇ q3)) ◇ t) (congrArg (fun t => (q4 ◇ q3) ◇ t) (apc1 q3 q4 q3))).symm).trans ((h (q4 ◇ q3) q5 q7 (q4 ◇ q3)).symm)).trans (apc2 q3 q4 q5 ((q4 ◇ q3) ◇ q5)))
  exact (calc
    (x ◇ y) = (x ◇ x):=apc0 x y x x
    _ = ((y ◇ (y ◇ z)) ◇ (y ◇ (y ◇ z))):=apc3 (y ◇ (y ◇ z)) x x x
    _ = ((y ◇ (y ◇ z)) ◇ x):=(apc0 (y ◇ (y ◇ z)) x x x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_46485_to_3967 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_46485_to_3967
