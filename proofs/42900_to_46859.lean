-- Equation42900 → Equation46859
-- Recorded verdict: true
-- Premise: x * y = y * (z * ((w * w) * x))
-- Conclusion: x * x = (y * x) * ((y * z) * x)
-- Original submission SHA-256: 83fe78b197f384d6090533cef61c2488a9018819bd5c0d71be3de5718d4c07c4
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = y ◇ (z ◇ ((w ◇ w) ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = (y ◇ x) ◇ ((y ◇ z) ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3:G), (((q0 ◇ q0) ◇ q1) ◇ q2) = (q2 ◇ (q1 ◇ q3)):=by
    intro q0 q1 q2 q3
    exact (((congrArg (fun t => q2 ◇ t) ((h q1 q3 (q0 ◇ q0) q0).symm)).symm).trans ((h ((q0 ◇ q0) ◇ q1) q2 q3 q0).symm)).symm
  have apc1 : forall (q4 q5 q6 q7:G), (((q4 ◇ q4) ◇ q7) ◇ q6) = (q5 ◇ q6):=by
    intro q4 q5 q6 q7
    exact (apc0 q4 q7 q6 ((q4 ◇ q4) ◇ q5)).trans ((h q5 q6 q7 q4).symm)
  have apc3 : forall (q8 q9 q10 q11:G), (q10 ◇ (q9 ◇ q11)) = (q8 ◇ q10):=by
    intro q8 q9 q10 q11
    exact (((apc1 q8 q8 q10 q9).symm).trans (apc0 q8 q9 q10 q11)).symm
  exact ((apc3 x y x x).symm).trans ((apc3 x (y ◇ z) (y ◇ x) x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_42900_to_46859 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_42900_to_46859
