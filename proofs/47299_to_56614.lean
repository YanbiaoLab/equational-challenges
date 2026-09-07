-- Equation47299 → Equation56614
-- Recorded verdict: true
-- Premise: x * y = (z * x) * ((x * x) * w)
-- Conclusion: x * (x * y) = (z * (z * w)) * u
-- Original submission SHA-256: ed647183640505f511b580fb1b2a49d1df5aceb6c2e010a86a3ca7e56d2485a0
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ x) ◇ ((x ◇ x) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ (x ◇ y) = (z ◇ (z ◇ w)) ◇ u
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (x y z w:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w
    exact (h x y z w).trans ((h x x z w).symm)
  have apc1 : forall (q0 q1 q2:G), ((q1 ◇ q0) ◇ (q1 ◇ q0)) = (q0 ◇ q0):=by
    intro q0 q1 q2
    exact (((apc0 (q1 ◇ q0) ((q0 ◇ q0) ◇ q0) q0 q0).symm).trans ((h q0 q2 q1 q0).symm)).trans (apc0 q0 q2 (q0 ◇ q2) (q0 ◇ q2))
  have apc2 : forall (q3 q4 q5 q6:G), ((q4 ◇ q3) ◇ q5) = (q3 ◇ q3):=by
    intro q3 q4 q5 q6
    exact (((((congrArg (fun t => (q3 ◇ q3) ◇ t) (congrArg (fun t => t ◇ q6) (apc1 q3 q4 ((q4 ◇ q3) ◇ (q4 ◇ q3))))).trans (apc0 (q3 ◇ q3) ((q3 ◇ q3) ◇ q6) ((q3 ◇ q3) ◇ ((q3 ◇ q3) ◇ q6)) ((q3 ◇ q3) ◇ ((q3 ◇ q3) ◇ q6)))).trans (apc1 q3 q3 ((q3 ◇ q3) ◇ (q3 ◇ q3)))).symm).trans (((congrArg (fun t => t ◇ (((q4 ◇ q3) ◇ (q4 ◇ q3)) ◇ q6)) (apc1 q3 q4 q3)).symm).trans ((h (q4 ◇ q3) q5 (q4 ◇ q3) q6).symm))).symm
  have apc3 : forall (q3 q7 q4 q6 q5:G), (q7 ◇ q7) = (q3 ◇ q3):=by
    intro q3 q7 q4 q6 q5
    exact ((((congrArg (fun t => (q7 ◇ (q4 ◇ q3)) ◇ t) (apc2 q3 q3 q6 ((q3 ◇ q3) ◇ q6))).trans (congrArg (fun t => t ◇ (q3 ◇ q3)) (apc0 q7 (q4 ◇ q3) (q7 ◇ (q4 ◇ q3)) (q7 ◇ (q4 ◇ q3))))).trans (apc2 q7 q7 (q3 ◇ q3) ((q7 ◇ q7) ◇ (q3 ◇ q3)))).symm).trans ((((congrArg (fun t => (q7 ◇ (q4 ◇ q3)) ◇ t) (congrArg (fun t => t ◇ q6) (apc1 q3 q4 q3))).symm).trans ((h (q4 ◇ q3) q5 q7 q6).symm)).trans (apc2 q3 q4 q5 ((q4 ◇ q3) ◇ q5)))
  exact (calc
    (x ◇ (x ◇ y)) = (x ◇ x):=apc0 x (x ◇ y) u u
    _ = ((z ◇ (z ◇ w)) ◇ (z ◇ (z ◇ w))):=apc3 (z ◇ (z ◇ w)) x u u u
    _ = ((z ◇ (z ◇ w)) ◇ u):=(apc0 (z ◇ (z ◇ w)) u u u).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_47299_to_56614 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_47299_to_56614
