-- Equation60604 → Equation60387
-- Recorded verdict: true
-- Premise: (x * y) * z = (y * w) * (u * v)
-- Conclusion: (x * y) * y = (z * x) * (w * y)
-- Original submission SHA-256: 5eb5888cd604276c4075a77895b4163b2f23d8de37ab00631d8006ee0b8962f6
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), (x ◇ y) ◇ z = (y ◇ w) ◇ (u ◇ v)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ y = (z ◇ x) ◇ (w ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc3 : forall (q0 q1 q2 q3 q4:G), ((q2 ◇ q3) ◇ q4) = ((q0 ◇ q3) ◇ q1):=by
    intro q0 q1 q2 q3 q4
    exact ((h q0 q3 q1 q0 q0 q0).trans ((h q2 q3 q4 q0 q0 q0).symm)).symm
  have apc5 : forall (q0 q1 q2 q3 q4:G), ((q2 ◇ q3) ◇ q2) = ((q0 ◇ q3) ◇ q1):=by
    intro q0 q1 q2 q3 q4
    exact (((apc3 q0 q1 q2 q3 q4).symm).trans (apc3 q2 q2 q2 q3 q4)).symm
  have apc7 : forall (q5 q6 q7 q8 q9:G), ((q7 ◇ q8) ◇ q9) = ((q5 ◇ q6) ◇ q5):=by
    intro q5 q6 q7 q8 q9
    exact ((apc5 q8 (q5 ◇ q5) q5 q6 q5).trans ((h q7 q8 q9 q6 q5 q5).symm)).symm
  exact (apc7 ((x ◇ y) ◇ y) ((z ◇ x) ◇ (w ◇ y)) x y y).trans ((apc7 ((x ◇ y) ◇ y) ((z ◇ x) ◇ (w ◇ y)) z x (w ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_60604_to_60387 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_60604_to_60387
