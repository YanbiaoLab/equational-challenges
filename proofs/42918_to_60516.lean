-- Equation42918 → Equation60516
-- Recorded verdict: true
-- Premise: x * y = z * (x * ((x * y) * w))
-- Conclusion: (x * y) * z = (x * w) * (z * u)
-- Original submission SHA-256: 5be470657a4c2228aec7f7aaa06eac83617069de669e02c0657dabcb38d2c1bb
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ (x ◇ ((x ◇ y) ◇ w))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), (x ◇ y) ◇ z = (x ◇ w) ◇ (z ◇ u)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1 q2 q3:G), (q3 ◇ ((q1 ◇ q2) ◇ q0)) = (q1 ◇ q2):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => q3 ◇ t) ((h (q1 ◇ q2) q0 q1 q0).symm)).symm).trans ((h q1 q2 q3 (((q1 ◇ q2) ◇ q0) ◇ q0)).symm)
  have apc1 : forall (q4 q5 q6:G), ((q4 ◇ q5) ◇ q6) = (q4 ◇ q5):=by
    intro q4 q5 q6
    exact (((apc0 (((q4 ◇ q5) ◇ q6) ◇ q4) q4 q5 q4).symm).trans ((h (q4 ◇ q5) q6 q4 q4).symm)).symm
  have apc4 : forall (q7 q8 q9 q10:G), (q9 ◇ q10) = (q7 ◇ q8):=by
    intro q7 q8 q9 q10
    exact (((apc1 q7 q8 (q9 ◇ ((q9 ◇ q10) ◇ q7))).symm).trans ((h q9 q10 (q7 ◇ q8) q7).symm)).symm
  exact (apc4 ((x ◇ y) ◇ z) ((x ◇ w) ◇ (z ◇ u)) (x ◇ y) z).trans ((apc4 ((x ◇ y) ◇ z) ((x ◇ w) ◇ (z ◇ u)) (x ◇ w) (z ◇ u)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_42918_to_60516 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_42918_to_60516
