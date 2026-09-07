-- Equation56322 → Equation55763
-- Recorded verdict: true
-- Premise: x ◇ (y ◇ z) = (w ◇ x) ◇ (u ◇ v)
-- Conclusion: x ◇ (x ◇ y) = (z ◇ w) ◇ (u ◇ v)
-- Original submission SHA-256: ac610493679f5ae49a1ea6fcbc039724133ab149473c20cc550ebb445500fdae
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x ◇ (y ◇ z) = (w ◇ x) ◇ (u ◇ v)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x ◇ (x ◇ y) = (z ◇ w) ◇ (u ◇ v)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u v
  have apc0 : forall (x y z w u v:G), ((x ◇ x) ◇ (x ◇ x)) = ((w ◇ x) ◇ (u ◇ v)):=by
    intro x y z w u v
    exact (((h x y z w u v).symm).trans (h x y z x x x)).symm
  have apc1 : forall (q0 q1 q2:G), ((q0 ◇ q0) ◇ (q0 ◇ q0)) = (q0 ◇ (q1 ◇ q2)):=by
    intro q0 q1 q2
    exact (apc0 q0 q0 q0 q0 q0 q0).trans ((h q0 q1 q2 q0 q0 q0).symm)
  have apc2 : forall (x y z w u v:G), (x ◇ (y ◇ z)) = (x ◇ (x ◇ x)):=by
    intro x y z w u v
    exact (h x y z w u v).trans ((h x x x w u v).symm)
  have apc6 : forall (q3 q4 q5 q6 q7 q8 q9:G), ((q7 ◇ (q3 ◇ q4)) ◇ (q5 ◇ q6)) = (q4 ◇ (q4 ◇ q4)):=by
    intro q3 q4 q5 q6 q7 q8 q9
    exact (((apc2 q4 q8 q9 (q4 ◇ (q8 ◇ q9)) (q4 ◇ (q8 ◇ q9)) (q4 ◇ (q8 ◇ q9))).symm).trans ((h q4 q8 q9 q3 q3 q3).trans (h (q3 ◇ q4) q3 q3 q7 q5 q6))).symm
  have apc7 : forall (q10 q11 q12 q13 q14 q15:G), (q13 ◇ (q10 ◇ q11)) = (q12 ◇ (q12 ◇ q12)):=by
    intro q10 q11 q12 q13 q14 q15
    exact (((apc1 q13 q10 q11).symm).trans (h (q13 ◇ q13) q13 q13 q12 q14 q15)).trans ((congrArg (fun t => t ◇ (q14 ◇ q15)) (apc2 q12 q13 q13 (q12 ◇ (q13 ◇ q13)) (q12 ◇ (q13 ◇ q13)) (q12 ◇ (q13 ◇ q13)))).trans (apc6 q12 q12 q14 q15 q12 ((q12 ◇ (q12 ◇ q12)) ◇ (q14 ◇ q15)) ((q12 ◇ (q12 ◇ q12)) ◇ (q14 ◇ q15))))
  exact (apc7 x y (x ◇ (x ◇ y)) x (x ◇ (x ◇ y)) (x ◇ (x ◇ y))).trans ((apc7 u v (x ◇ (x ◇ y)) (z ◇ w) (x ◇ (x ◇ y)) (x ◇ (x ◇ y))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_56322_to_55763 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_56322_to_55763
