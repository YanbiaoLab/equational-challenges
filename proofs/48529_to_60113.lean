-- Equation48529 → Equation60113
-- Recorded verdict: true
-- Premise: x * y = (z * (w * u)) * (w * w)
-- Conclusion: (x * x) * y = (z * z) * (y * w)
-- Original submission SHA-256: b4253db3019255bef34c1c2378a56ae25fab9b7909ab8c41e58b1eca3adbd43a
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = (z ◇ (w ◇ u)) ◇ (w ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ x) ◇ y = (z ◇ z) ◇ (y ◇ w)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3 q4:G), ((q0 ◇ q1) ◇ (q2 ◇ q2)) = (q3 ◇ q4):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => t ◇ (q2 ◇ q2)) ((h q0 q1 q0 q2 q0).symm)).symm).trans ((h q3 q4 (q0 ◇ (q2 ◇ q0)) q2 q2).symm)
  have apc2 : forall (q0 q1 q2 q3 q4:G), ((q3 ◇ q3) ◇ (q3 ◇ q3)) = ((q0 ◇ q1) ◇ (q2 ◇ q2)):=by
    intro q0 q1 q2 q3 q4
    exact ((apc0 q0 q1 q2 q3 q4).trans ((apc0 q3 q3 q3 q3 q4).symm)).symm
  have apc3 : forall (q5 q6 q7:G), ((q5 ◇ q5) ◇ (q5 ◇ q5)) = (q6 ◇ q7):=by
    intro q5 q6 q7
    exact (apc2 q5 q5 q5 q5 q5).trans (apc0 q5 q5 q5 q6 q7)
  exact ((apc3 ((x ◇ x) ◇ y) (x ◇ x) y).symm).trans (apc3 ((x ◇ x) ◇ y) (z ◇ z) (y ◇ w))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_48529_to_60113 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_48529_to_60113
