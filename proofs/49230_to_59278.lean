-- Equation49230 → Equation59278
-- Recorded verdict: true
-- Premise: x * y = ((z * z) * y) * (z * y)
-- Conclusion: (x * y) * x = x * ((x * z) * x)
-- Original submission SHA-256: f8e3b105134d4206e5b240a926e6150f70dac7f013fdd2e2698cdee39a136a6e
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((z ◇ z) ◇ y) ◇ (z ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ x = x ◇ ((x ◇ z) ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z:G), (y ◇ y) = (x ◇ y):=by
    intro x y z
    exact ((h x y z).trans ((h y y z).symm)).symm
  have apc1 : forall (q0 q1 q2:G), (q1 ◇ q2) = (q0 ◇ q2):=by
    intro q0 q1 q2
    exact ((h q0 q2 q0).trans ((h q1 q2 q0).symm)).symm
  have apc2 : forall (q3 q4 q5 q6:G), (q3 ◇ (q6 ◇ q5)) = (q4 ◇ q5):=by
    intro q3 q4 q5 q6
    exact ((apc1 q3 ((q6 ◇ q6) ◇ q5) (q6 ◇ q5)).symm).trans ((h q4 q5 q6).symm)
  have apc3 : forall (q7 q8 q9:G), (q7 ◇ (q8 ◇ q9)) = (q9 ◇ q9):=by
    intro q7 q8 q9
    exact (apc2 q7 q7 q9 q8).trans ((apc0 q7 q9 q7).symm)
  exact (calc
    ((x ◇ y) ◇ x) = (x ◇ x):=(apc0 (x ◇ y) x x).symm
    _ = (x ◇ ((x ◇ z) ◇ x)):=(apc3 x (x ◇ z) x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_49230_to_59278 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_49230_to_59278
