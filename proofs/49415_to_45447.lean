-- Equation49415 → Equation45447
-- Recorded verdict: true
-- Premise: x * y = ((z * w) * u) * (v * x)
-- Conclusion: x * y = y * (((y * y) * z) * w)
-- Original submission SHA-256: cba6013fd906eaea541c820b51ea69fb001d9d84289ded99a02677b258a3ab1e
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x ◇ y = ((z ◇ w) ◇ u) ◇ (v ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = y ◇ (((y ◇ y) ◇ z) ◇ w)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w u v:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w u v
    exact (h x y z w u v).trans ((h x x z w u v).symm)
  have apc1 : forall (q0 q1 q2 q3 q4:G), ((q0 ◇ q0) ◇ (q0 ◇ q0)) = (q1 ◇ q1):=by
    intro q0 q1 q2 q3 q4
    exact ((((congrArg (fun t => t ◇ (q2 ◇ q1)) (apc0 q0 q3 (q0 ◇ q3) (q0 ◇ q3) (q0 ◇ q3) (q0 ◇ q3))).trans (congrArg (fun t => (q0 ◇ q0) ◇ t) (apc0 q2 q1 (q2 ◇ q1) (q2 ◇ q1) (q2 ◇ q1) (q2 ◇ q1)))).trans (apc0 (q0 ◇ q0) (q2 ◇ q2) ((q0 ◇ q0) ◇ (q2 ◇ q2)) ((q0 ◇ q0) ◇ (q2 ◇ q2)) ((q0 ◇ q0) ◇ (q2 ◇ q2)) ((q0 ◇ q0) ◇ (q2 ◇ q2)))).symm).trans ((((congrArg (fun t => t ◇ (q2 ◇ q1)) ((h q0 q3 q0 q0 q0 q0).symm)).symm).trans ((h q1 q4 (q0 ◇ q0) q0 (q0 ◇ q0) q2).symm)).trans (apc0 q1 q4 (q1 ◇ q4) (q1 ◇ q4) (q1 ◇ q4) (q1 ◇ q4)))
  have apc2 : forall (q0 q3 q2 q1 q4:G), (q1 ◇ q1) = (q0 ◇ q0):=by
    intro q0 q3 q2 q1 q4
    exact ((apc1 q0 q1 q2 q3 q4).symm).trans (apc1 q0 q0 q2 q3 q4)
  have apc3 : forall (q5 q6 q7:G), ((q6 ◇ q6) ◇ (q5 ◇ q5)) = (q7 ◇ q7):=by
    intro q5 q6 q7
    exact ((congrArg (fun t => (q6 ◇ q6) ◇ t) (apc2 q5 q5 q5 q6 q5)).symm).trans (apc1 q6 q7 q5 q5 q5)
  have apc5 : forall (q8 q9 q10:G), (q10 ◇ q10) = (q9 ◇ q8):=by
    intro q8 q9 q10
    exact ((h q9 q8 q8 q8 (q8 ◇ q8) q9).trans (apc3 q9 (q8 ◇ q8) q10)).symm
  exact ((apc5 y x (x ◇ y)).symm).trans (apc5 (((y ◇ y) ◇ z) ◇ w) y (x ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_49415_to_45447 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_49415_to_45447
