-- Equation52753 → Equation56676
-- Recorded verdict: true
-- Premise: x * y = ((z * (z * z)) * y) * w
-- Conclusion: x * (y * x) = (x * (z * w)) * w
-- Original submission SHA-256: 3387091a08808722d60ea42811938c5728e420ee4679e38c4fc052797d912db2
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ (z ◇ z)) ◇ y) ◇ w
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ x) = (x ◇ (z ◇ w)) ◇ w
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2:G), (q1 ◇ q2) = (q0 ◇ q2):=by
    intro q0 q1 q2
    exact ((h q0 q2 q0 q0).trans ((h q1 q2 q0 q0).symm)).symm
  have apc2 : forall (q3 q4 q5 q6:G), (q5 ◇ q6) = (q3 ◇ q4):=by
    intro q3 q4 q5 q6
    exact (((apc0 q3 ((q3 ◇ (q3 ◇ q3)) ◇ q6) q4).symm).trans ((h q5 q6 q3 q4).symm)).symm
  exact (apc2 (x ◇ (y ◇ x)) ((x ◇ (z ◇ w)) ◇ w) x (y ◇ x)).trans ((apc2 (x ◇ (y ◇ x)) ((x ◇ (z ◇ w)) ◇ w) (x ◇ (z ◇ w)) w).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_52753_to_56676 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_52753_to_56676
