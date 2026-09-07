-- Equation42324 → Equation60621
-- Recorded verdict: true
-- Premise: x * y = z * (w * (z * (y * z)))
-- Conclusion: (x * y) * z = (z * x) * (w * u)
-- Original submission SHA-256: 12a8770af4360f1ff7ef5668ce42ce99cf777138316c92aa6c5dfc4869a9e81d
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ (w ◇ (z ◇ (y ◇ z)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), (x ◇ y) ◇ z = (z ◇ x) ◇ (w ◇ u)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1 q2:G), (q1 ◇ q2) = (q0 ◇ q2):=by
    intro q0 q1 q2
    exact ((h q0 q2 q0 q0).trans ((h q1 q2 q0 q0).symm)).symm
  have apc2 : forall (q0 q3 q1 q2:G), ((q3 ◇ q2) ◇ (q0 ◇ q3)) = (q1 ◇ q2):=by
    intro q0 q3 q1 q2
    exact ((congrArg (fun t => (q3 ◇ q2) ◇ t) ((h q0 q3 q2 (q3 ◇ q2)).symm)).symm).trans ((h q1 q2 (q3 ◇ q2) q2).symm)
  have apc3 : forall (q4 q5 q6 q7 q8:G), (q8 ◇ (q4 ◇ q5)) = (q6 ◇ q7):=by
    intro q4 q5 q6 q7 q8
    exact (((apc2 q4 q5 q6 q7).symm).trans (apc0 q8 (q5 ◇ q7) (q4 ◇ q5))).symm
  have apc4 : forall (q9 q10 q11 q12:G), (q11 ◇ q12) = (q9 ◇ q10):=by
    intro q9 q10 q11 q12
    exact (((apc3 q9 q9 q9 q10 (q9 ◇ q12)).symm).trans (apc2 q9 q9 q11 q12)).symm
  exact (apc4 ((x ◇ y) ◇ z) ((z ◇ x) ◇ (w ◇ u)) (x ◇ y) z).trans ((apc4 ((x ◇ y) ◇ z) ((z ◇ x) ◇ (w ◇ u)) (z ◇ x) (w ◇ u)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_42324_to_60621 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_42324_to_60621
