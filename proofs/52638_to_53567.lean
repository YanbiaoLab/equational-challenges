-- Equation52638 → Equation53567
-- Recorded verdict: true
-- Premise: x * y = ((z * (y * x)) * x) * w
-- Conclusion: x * y = (((z * y) * w) * x) * u
-- Original submission SHA-256: 2d513beba1c016306ffbab5888164295fcd43108c51ed21f25880f4d0f0f7adf
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ (y ◇ x)) ◇ x) ◇ w
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = (((z ◇ y) ◇ w) ◇ x) ◇ u
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1 q2 q3:G), (((q3 ◇ q2) ◇ q0) ◇ q1) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ q1) ((h (q3 ◇ q2) q0 q0 q2).symm)).symm).trans ((h q2 q3 (q0 ◇ (q0 ◇ (q3 ◇ q2))) q1).symm)
  have apc1 : forall (q4 q5 q6:G), ((q5 ◇ q4) ◇ q6) = (q4 ◇ q5):=by
    intro q4 q5 q6
    exact ((apc0 q4 q4 (q5 ◇ q4) q6).symm).trans ((h q4 q5 q6 q4).symm)
  have apc2 : forall (q7 q0 q2 q3 q1:G), (q2 ◇ q3) = (q7 ◇ q0):=by
    intro q7 q0 q2 q3 q1
    exact ((((congrArg (fun t => t ◇ q1) (apc1 q0 q7 q2)).trans (apc1 q7 q0 q1)).symm).trans (((congrArg (fun t => t ◇ q1) (congrArg (fun t => t ◇ q2) ((h q7 q0 q7 (q3 ◇ q2)).symm))).symm).trans ((h q2 q3 ((q7 ◇ (q0 ◇ q7)) ◇ q7) q1).symm))).symm
  exact (apc2 (x ◇ y) ((((z ◇ y) ◇ w) ◇ x) ◇ u) x y (x ◇ y)).trans ((apc2 (x ◇ y) ((((z ◇ y) ◇ w) ◇ x) ◇ u) (((z ◇ y) ◇ w) ◇ x) u (x ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_52638_to_53567 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_52638_to_53567
