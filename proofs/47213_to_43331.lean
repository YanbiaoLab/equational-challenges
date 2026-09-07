-- Equation47213 → Equation43331
-- Recorded verdict: true
-- Premise: x * y = (y * y) * ((z * z) * w)
-- Conclusion: x * x = x * ((y * z) * (w * y))
-- Original submission SHA-256: 834cbcac767fe216b5d6ee00f74d03f30c85ee93465ade08b61e86edc9fee61a
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (y ◇ y) ◇ ((z ◇ z) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = x ◇ ((y ◇ z) ◇ (w ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w:G), (y ◇ y) = (x ◇ y):=by
    intro x y z w
    exact ((h x y z w).trans ((h y y z w).symm)).symm
  have apc1 : forall (q0 q1 q2:G), (q0 ◇ ((q2 ◇ q2) ◇ (q2 ◇ q2))) = (q1 ◇ (q2 ◇ q2)):=by
    intro q0 q1 q2
    exact ((apc0 q0 ((q2 ◇ q2) ◇ (q2 ◇ q2)) q0 q0).symm).trans ((h q1 (q2 ◇ q2) q2 (q2 ◇ q2)).symm)
  have apc6 : forall (q3 q4 q5 q6:G), (q4 ◇ ((q6 ◇ q6) ◇ (q6 ◇ q6))) = (q5 ◇ (q3 ◇ q6)):=by
    intro q3 q4 q5 q6
    exact (((congrArg (fun t => q5 ◇ t) (apc0 q3 q6 q3 q3)).symm).trans ((apc1 q4 q5 q6).symm)).symm
  have apc7 : forall (q7 q8 q9 q10:G), (q7 ◇ ((q8 ◇ q8) ◇ (q8 ◇ q8))) = (q9 ◇ q10):=by
    intro q7 q8 q9 q10
    exact (apc6 (q7 ◇ q7) q7 (q10 ◇ q10) q8).trans ((h q9 q10 q7 q8).symm)
  exact ((apc7 (x ◇ ((y ◇ z) ◇ (w ◇ y))) (x ◇ x) x x).symm).trans (apc7 (x ◇ ((y ◇ z) ◇ (w ◇ y))) (x ◇ x) x ((y ◇ z) ◇ (w ◇ y)))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_47213_to_43331 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_47213_to_43331
