-- Equation48330 → Equation59092
-- Recorded verdict: true
-- Premise: x * y = (z * (z * x)) * (x * w)
-- Conclusion: (x * x) * x = y * ((x * z) * z)
-- Original submission SHA-256: 0e5910e46f1f43c5bd5119a48c57509cc63ccf56b76e450357d91037f86ff4a8
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ (z ◇ x)) ◇ (x ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ x) ◇ x = y ◇ ((x ◇ z) ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z w:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w
    exact (h x y z w).trans ((h x x z w).symm)
  have apc1 : forall (q0 q1 q2:G), ((q1 ◇ q1) ◇ (q1 ◇ q1)) = (q0 ◇ q0):=by
    intro q0 q1 q2
    exact (((congrArg (fun t => t ◇ (q1 ◇ (q1 ◇ q0))) (apc0 q1 (q1 ◇ q0) (q1 ◇ (q1 ◇ q0)) (q1 ◇ (q1 ◇ q0)))).trans (congrArg (fun t => (q1 ◇ q1) ◇ t) (apc0 q1 (q1 ◇ q0) (q1 ◇ (q1 ◇ q0)) (q1 ◇ (q1 ◇ q0))))).symm).trans ((((apc0 (q1 ◇ (q1 ◇ q0)) (q0 ◇ q0) q0 q0).symm).trans ((h q0 q2 q1 q0).symm)).trans (apc0 q0 q2 (q0 ◇ q2) (q0 ◇ q2)))
  have apc2 : forall (q0 q2 q1:G), (q1 ◇ q1) = (q0 ◇ q0):=by
    intro q0 q2 q1
    exact (((apc1 q0 q1 q2).symm).trans (apc1 q1 q1 q2)).symm
  have apc3 : forall (q3 q4 q5:G), (q5 ◇ q5) = (q4 ◇ q3):=by
    intro q3 q4 q5
    exact ((h q4 q3 q4 (q4 ◇ q4)).trans (apc2 q5 q3 (q4 ◇ (q4 ◇ q4)))).symm
  exact ((apc3 x (x ◇ x) ((x ◇ x) ◇ x)).symm).trans (apc3 ((x ◇ z) ◇ z) y ((x ◇ x) ◇ x))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_48330_to_59092 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_48330_to_59092
