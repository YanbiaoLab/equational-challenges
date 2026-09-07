-- Equation42939 → Equation43920
-- Recorded verdict: true
-- Premise: x * y = z * (x * ((y * z) * w))
-- Conclusion: x * y = z * ((y * w) * (x * u))
-- Original submission SHA-256: c6a5695379f4e71337c2d56d53ad7e0a37917d2a1416b47d820c76160a057df0
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ (x ◇ ((y ◇ z) ◇ w))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = z ◇ ((y ◇ w) ◇ (x ◇ u))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1 q2 q3:G), (q3 ◇ ((q2 ◇ q3) ◇ q0)) = (q1 ◇ q2):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => q3 ◇ t) ((h (q2 ◇ q3) q0 q1 q0).symm)).symm).trans ((h q1 q2 q3 ((q0 ◇ q1) ◇ q0)).symm)
  have apc1 : forall (q4 q0 q1 q2 q3:G), (q3 ◇ (q1 ◇ (q4 ◇ q0))) = (q1 ◇ q2):=by
    intro q4 q0 q1 q2 q3
    exact ((congrArg (fun t => q3 ◇ t) (congrArg (fun t => q1 ◇ t) ((h q4 q0 (q2 ◇ q3) q4).symm))).symm).trans ((h q1 q2 q3 (q4 ◇ ((q0 ◇ (q2 ◇ q3)) ◇ q4))).symm)
  have apc2 : forall (q5 q6 q7 q8 q9 q10:G), (q7 ◇ (q10 ◇ (q5 ◇ q6))) = (q8 ◇ q9):=by
    intro q5 q6 q7 q8 q9 q10
    exact (apc1 q5 q6 q10 ((q9 ◇ q10) ◇ q5) q7).trans (apc0 q5 q8 q9 q10)
  have apc12 : forall (q5 q6 q7 q8 q9 q10:G), (q8 ◇ q9) = (q5 ◇ q5):=by
    intro q5 q6 q7 q8 q9 q10
    exact ((apc2 q5 q6 q7 q8 q9 q10).symm).trans (apc2 q5 q6 q7 q5 q5 q10)
  exact (apc12 (x ◇ y) (x ◇ y) (x ◇ y) x y (x ◇ y)).trans ((apc12 (x ◇ y) (x ◇ y) (x ◇ y) z ((y ◇ w) ◇ (x ◇ u)) (x ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_42939_to_43920 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_42939_to_43920
