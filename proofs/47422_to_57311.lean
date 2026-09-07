-- Equation47422 → Equation57311
-- Recorded verdict: true
-- Premise: x * y = (z * y) * ((z * w) * w)
-- Conclusion: x * (y * z) = (w * (u * v)) * w
-- Original submission SHA-256: 145ac53e2f0b19cd73f461ae0d4a98cb111f701ebd56b04424dc10ab9b344358
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ y) ◇ ((z ◇ w) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x ◇ (y ◇ z) = (w ◇ (u ◇ v)) ◇ w
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u v
  have apc1 : forall (q0 q1 q2:G), (q1 ◇ q2) = (q0 ◇ q2):=by
    intro q0 q1 q2
    exact ((h q0 q2 q0 q0).trans ((h q1 q2 q0 q0).symm)).symm
  have apc2 : forall (q3 q4 q5 q6 q7:G), (q3 ◇ ((q7 ◇ q4) ◇ q4)) = (q5 ◇ q6):=by
    intro q3 q4 q5 q6 q7
    exact ((apc1 q3 (q7 ◇ q6) ((q7 ◇ q4) ◇ q4)).symm).trans ((h q5 q6 q7 q4).symm)
  have apc8 : forall (q3 q4 q5 q6 q7:G), (q5 ◇ q6) = (q3 ◇ q3):=by
    intro q3 q4 q5 q6 q7
    exact ((apc2 q3 q4 q5 q6 q7).symm).trans (apc2 q3 q4 q3 q3 q7)
  exact (apc8 (x ◇ (y ◇ z)) (x ◇ (y ◇ z)) x (y ◇ z) (x ◇ (y ◇ z))).trans ((apc8 (x ◇ (y ◇ z)) (x ◇ (y ◇ z)) (w ◇ (u ◇ v)) w (x ◇ (y ◇ z))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_47422_to_57311 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_47422_to_57311
