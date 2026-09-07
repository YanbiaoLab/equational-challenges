-- Equation49168 → Equation56321
-- Recorded verdict: true
-- Premise: x * y = ((z * y) * z) * (y * w)
-- Conclusion: x * (y * z) = (w * x) * (u * u)
-- Original submission SHA-256: 6d15be13b5b8433bc2b402412b66ccd1a14ee12bb6af452d2d00fbb8a5e89c9c
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ y) ◇ z) ◇ (y ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ (y ◇ z) = (w ◇ x) ◇ (u ◇ u)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1 q2:G), (q1 ◇ q2) = (q0 ◇ q2):=by
    intro q0 q1 q2
    exact ((h q0 q2 q0 q0).trans ((h q1 q2 q0 q0).symm)).symm
  have apc2 : forall (q3 q4 q5 q6:G), (q3 ◇ (q6 ◇ q4)) = (q5 ◇ q6):=by
    intro q3 q4 q5 q6
    exact ((apc0 q3 ((q3 ◇ q6) ◇ q3) (q6 ◇ q4)).symm).trans ((h q5 q6 q3 q4).symm)
  have apc4 : forall (q7 q8 q9 q10 q11:G), (q9 ◇ (q7 ◇ q8)) = (q10 ◇ q11):=by
    intro q7 q8 q9 q10 q11
    exact ((congrArg (fun t => q9 ◇ t) (apc2 q11 q7 q7 q8)).symm).trans (apc2 q9 (q8 ◇ q7) q10 q11)
  have apc7 : forall (q7 q10 q11 q8 q9:G), (q10 ◇ q11) = (q7 ◇ q7):=by
    intro q7 q10 q11 q8 q9
    exact ((apc4 q7 q8 q9 q10 q11).symm).trans (apc4 q7 q8 q9 q7 q7)
  exact (apc7 (x ◇ (y ◇ z)) x (y ◇ z) (x ◇ (y ◇ z)) (x ◇ (y ◇ z))).trans ((apc7 (x ◇ (y ◇ z)) (w ◇ x) (u ◇ u) (x ◇ (y ◇ z)) (x ◇ (y ◇ z))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_49168_to_56321 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_49168_to_56321
