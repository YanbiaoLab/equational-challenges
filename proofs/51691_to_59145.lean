-- Equation51691 → Equation59145
-- Recorded verdict: true
-- Premise: x * y = ((z * x) * (x * z)) * z
-- Conclusion: (x * x) * y = x * ((z * y) * x)
-- Original submission SHA-256: 191b6fd2c5aa713e3c8c589e4cd881d00cb1848d0337049096731dccfad5cc2a
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((z ◇ x) ◇ (x ◇ z)) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ x) ◇ y = x ◇ ((z ◇ y) ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z:G), (x ◇ y) = (x ◇ x):=by
    intro x y z
    exact (h x y z).trans ((h x x z).symm)
  have apc1 : forall (q0 q1 q2:G), (((q1 ◇ q0) ◇ (q1 ◇ q0)) ◇ q1) = (q0 ◇ q0):=by
    intro q0 q1 q2
    exact (((congrArg (fun t => t ◇ q1) (apc0 (q1 ◇ q0) (q0 ◇ q1) q0)).symm).trans ((h q0 q2 q1).symm)).trans (apc0 q0 q2 (q0 ◇ q2))
  have apc2 : forall (q3 q4 q5:G), ((q3 ◇ q3) ◇ q5) = (q4 ◇ q4):=by
    intro q3 q4 q5
    exact ((((congrArg (fun t => t ◇ q5) (congrArg (fun t => t ◇ q3) (congrArg (fun t => t ◇ ((q5 ◇ q4) ◇ q3)) (apc0 q3 (q5 ◇ q4) (q3 ◇ (q5 ◇ q4)))))).trans (congrArg (fun t => t ◇ q5) (congrArg (fun t => t ◇ q3) (apc0 (q3 ◇ q3) ((q5 ◇ q4) ◇ q3) ((q3 ◇ q3) ◇ ((q5 ◇ q4) ◇ q3)))))).trans (congrArg (fun t => t ◇ q5) (apc1 q3 q3 (((q3 ◇ q3) ◇ (q3 ◇ q3)) ◇ q3)))).symm).trans (((congrArg (fun t => t ◇ q5) (h (q5 ◇ q4) (q5 ◇ q4) q3)).symm).trans (apc1 q4 q5 q3))
  have apc5 : forall (q6 q7 q8:G), (q8 ◇ q6) = (q7 ◇ q7):=by
    intro q6 q7 q8
    exact (h q8 q6 q8).trans (apc2 (q8 ◇ q8) q7 q8)
  exact (apc5 y ((x ◇ x) ◇ y) (x ◇ x)).trans ((apc5 ((z ◇ y) ◇ x) ((x ◇ x) ◇ y) x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_51691_to_59145 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_51691_to_59145
