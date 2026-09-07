-- Equation53746 → Equation58501
-- Recorded verdict: true
-- Premise: x * y = (((z * w) * w) * x) * z
-- Conclusion: (x * y) * x = z * (y * (w * w))
-- Original submission SHA-256: e1fc0dc815d68c2040e3d2f4dbe2cd42fbf64ec643996bd6e64acbeb9917bbfb
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (((z ◇ w) ◇ w) ◇ x) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ x = z ◇ (y ◇ (w ◇ w))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc1 : forall (x y z w:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w
    exact (h x y z w).trans ((h x x z w).symm)
  have apc2 : forall (q0 q1 q2 q3:G), ((q1 ◇ q0) ◇ (q1 ◇ q0)) = (q2 ◇ q2):=by
    intro q0 q1 q2 q3
    exact ((apc1 (q1 ◇ q0) (q2 ◇ q1) ((q1 ◇ q0) ◇ (q2 ◇ q1)) ((q1 ◇ q0) ◇ (q2 ◇ q1))).symm).trans ((((congrArg (fun t => t ◇ (q2 ◇ q1)) ((h q1 q0 q2 q1).symm)).symm).trans ((h q2 q3 (q2 ◇ q1) q1).symm)).trans (apc1 q2 q3 (q2 ◇ q3) (q2 ◇ q3)))
  have apc10 : forall (q4 q5 q6 q7:G), (((q7 ◇ q5) ◇ q5) ◇ q6) = ((q4 ◇ q4) ◇ q7):=by
    intro q4 q5 q6 q7
    exact (((congrArg (fun t => t ◇ q7) (apc2 q5 (q7 ◇ q5) q4 q4)).symm).trans ((h ((q7 ◇ q5) ◇ q5) q6 q7 q5).symm)).symm
  have apc13 : forall (q8 q9 q10 q11:G), ((q9 ◇ q9) ◇ (q9 ◇ q9)) = (q10 ◇ q8):=by
    intro q8 q9 q10 q11
    exact (((h q10 q8 q11 q10).trans (apc10 q9 q10 q11 (q11 ◇ q10))).trans (apc1 (q9 ◇ q9) (q11 ◇ q10) ((q9 ◇ q9) ◇ (q11 ◇ q10)) ((q9 ◇ q9) ◇ (q11 ◇ q10)))).symm
  exact ((apc13 x ((x ◇ y) ◇ x) (x ◇ y) ((x ◇ y) ◇ x)).symm).trans (apc13 (y ◇ (w ◇ w)) ((x ◇ y) ◇ x) z ((x ◇ y) ◇ x))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_53746_to_58501 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_53746_to_58501
