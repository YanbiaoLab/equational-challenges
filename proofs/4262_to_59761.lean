-- Equation4262 → Equation59761
-- Recorded verdict: true
-- Premise: x * y = ((z * w) * u) * x
-- Conclusion: (x * y) * z = z * ((y * w) * u)
-- Original submission SHA-256: fd4312e857390a844e887dfe098a1ff64412f70380ddedda764c706eb2c3a849
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = ((z ◇ w) ◇ u) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), (x ◇ y) ◇ z = z ◇ ((y ◇ w) ◇ u)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1 q2 q3:G), ((q1 ◇ q0) ◇ q2) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ q2) ((h q1 q0 q0 q0 q0).symm)).symm).trans ((h q2 q3 (q0 ◇ q0) q0 q1).symm)
  have apc1 : forall (x y z w u:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w u
    exact (h x y z w u).trans ((h x x z w u).symm)
  have apc2 : forall (x y z w u q0 q1 q2 q3:G), ((q1 ◇ q0) ◇ q2) = (q2 ◇ q2):=by
    intro x y z w u q0 q1 q2 q3
    exact (apc0 q0 q1 q2 q3).trans (apc1 q2 q3 (q2 ◇ q3) (q2 ◇ q3) (q2 ◇ q3))
  have apc3 : forall (q4 q5 q6 q7 q8 q9:G), ((q5 ◇ q4) ◇ (q5 ◇ q4)) = (q7 ◇ q6):=by
    intro q4 q5 q6 q7 q8 q9
    exact ((((apc0 q4 q5 q7 q6).symm).trans ((apc0 q8 q9 (q5 ◇ q4) q7).symm)).trans (apc2 ((q9 ◇ q8) ◇ (q5 ◇ q4)) ((q9 ◇ q8) ◇ (q5 ◇ q4)) ((q9 ◇ q8) ◇ (q5 ◇ q4)) ((q9 ◇ q8) ◇ (q5 ◇ q4)) ((q9 ◇ q8) ◇ (q5 ◇ q4)) q8 q9 (q5 ◇ q4) ((q9 ◇ q8) ◇ (q5 ◇ q4)))).symm
  exact ((apc3 ((x ◇ y) ◇ z) (z ◇ ((y ◇ w) ◇ u)) z (x ◇ y) ((x ◇ y) ◇ z) ((x ◇ y) ◇ z)).symm).trans (apc3 ((x ◇ y) ◇ z) (z ◇ ((y ◇ w) ◇ u)) ((y ◇ w) ◇ u) z ((x ◇ y) ◇ z) ((x ◇ y) ◇ z))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_4262_to_59761 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_4262_to_59761
