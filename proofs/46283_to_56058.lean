-- Equation46283 → Equation56058
-- Recorded verdict: true
-- Premise: x * y = (y * x) * (y * (y * z))
-- Conclusion: x * (y * y) = (z * w) * (w * w)
-- Original submission SHA-256: 94670c6b9d5cfc7809e60cc9ccc466b3b4fe7291e0c1aa53f932ffc25eadd1c7
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (y ◇ x) ◇ (y ◇ (y ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ y) = (z ◇ w) ◇ (w ◇ w)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z:G), ((y ◇ x) ◇ (y ◇ (y ◇ z))) = ((y ◇ x) ◇ (y ◇ (y ◇ x))):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have apc1 : forall (q0 q1:G), ((q1 ◇ q0) ◇ (q1 ◇ (q1 ◇ q0))) = (q0 ◇ q1):=by
    intro q0 q1
    exact ((apc0 q0 q1 q0).symm).trans ((h q0 q1 q0).symm)
  have apc2 : forall (q2 q3 q0:G), (((q3 ◇ q2) ◇ q0) ◇ ((q3 ◇ q2) ◇ (q2 ◇ q3))) = (q0 ◇ (q3 ◇ q2)):=by
    intro q2 q3 q0
    exact ((congrArg (fun t => ((q3 ◇ q2) ◇ q0) ◇ t) (congrArg (fun t => (q3 ◇ q2) ◇ t) (apc1 q2 q3))).symm).trans (((congrArg (fun t => ((q3 ◇ q2) ◇ q0) ◇ t) (congrArg (fun t => (q3 ◇ q2) ◇ t) (apc0 q2 q3 q2))).symm).trans ((h q0 (q3 ◇ q2) (q3 ◇ (q3 ◇ q2))).symm))
  have apc4 : forall (q4 q5:G), ((((q4 ◇ q4) ◇ (q4 ◇ q4)) ◇ q5) ◇ ((q4 ◇ q4) ◇ (q4 ◇ q4))) = (q5 ◇ ((q4 ◇ q4) ◇ (q4 ◇ q4))):=by
    intro q4 q5
    exact ((congrArg (fun t => (((q4 ◇ q4) ◇ (q4 ◇ q4)) ◇ q5) ◇ t) (apc2 q4 q4 (q4 ◇ q4))).symm).trans (apc2 (q4 ◇ q4) (q4 ◇ q4) q5)
  have apc6 : forall (q6 q7:G), (((q7 ◇ q7) ◇ q6) ◇ (q7 ◇ q7)) = ((q7 ◇ q7) ◇ (q7 ◇ q7)):=by
    intro q6 q7
    exact (((apc2 q7 q7 (q7 ◇ q7)).symm).trans ((((congrArg (fun t => t ◇ ((q7 ◇ q7) ◇ (q7 ◇ q7))) ((h (q7 ◇ q7) (q7 ◇ q7) q6).symm)).symm).trans (apc4 q7 ((q7 ◇ q7) ◇ ((q7 ◇ q7) ◇ q6)))).trans (apc2 q7 q7 ((q7 ◇ q7) ◇ q6)))).symm
  have apc7 : forall (q4 q5:G), (q5 ◇ ((q4 ◇ q4) ◇ (q4 ◇ q4))) = ((q4 ◇ q4) ◇ (q4 ◇ q4)):=by
    intro q4 q5
    exact (((apc2 q4 q4 (q4 ◇ q4)).symm).trans (((apc6 q5 (q4 ◇ q4)).symm).trans (apc4 q4 q5))).symm
  have apc8 : forall (q8 q9 q10:G), ((q8 ◇ q8) ◇ (q8 ◇ q8)) = (q9 ◇ q10):=by
    intro q8 q9 q10
    exact (((congrArg (fun t => (q10 ◇ q9) ◇ t) (apc7 q8 q10)).trans (apc7 q8 (q10 ◇ q9))).symm).trans (((congrArg (fun t => (q10 ◇ q9) ◇ t) (congrArg (fun t => q10 ◇ t) (apc7 q8 q10))).symm).trans ((h q9 q10 ((q8 ◇ q8) ◇ (q8 ◇ q8))).symm))
  exact ((apc8 (x ◇ (y ◇ y)) x (y ◇ y)).symm).trans (apc8 (x ◇ (y ◇ y)) (z ◇ w) (w ◇ w))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_46283_to_56058 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_46283_to_56058
