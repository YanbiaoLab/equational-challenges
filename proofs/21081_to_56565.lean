-- Equation21081 → Equation56565
-- Recorded verdict: true
-- Premise: x = (y ◇ z) ◇ (((y ◇ y) ◇ x) ◇ y)
-- Conclusion: x ◇ (x ◇ y) = (z ◇ (x ◇ x)) ◇ y
-- Original submission SHA-256: 6fcaee629b194a804f38f28d96ac7f6a9cc76ac2e7c15c5aef170723ffb41890
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ z) ◇ (((y ◇ y) ◇ x) ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (x ◇ y) = (z ◇ (x ◇ x)) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), (((q1 ◇ q1) ◇ q0) ◇ q1) = ((q1 ◇ q2) ◇ (q0 ◇ q1)):=by
    intro q0 q1 q2
    exact (((congrArg (fun t => (q1 ◇ q2) ◇ t) (congrArg (fun t => t ◇ q1) ((h q0 q1 q1).symm))).symm).trans ((h (((q1 ◇ q1) ◇ q0) ◇ q1) q1 q2).symm)).symm
  have apc4 : forall (q3 q4:G), (((q4 ◇ q4) ◇ ((q4 ◇ q4) ◇ q3)) ◇ q4) = q3:=by
    intro q3 q4
    exact (apc0 ((q4 ◇ q4) ◇ q3) q4 q3).trans ((h q3 q4 q3).symm)
  have apc6 : forall (q5 q6 q7:G), ((q6 ◇ q7) ◇ q5) = ((q6 ◇ q6) ◇ q5):=by
    intro q5 q6 q7
    exact ((congrArg (fun t => (q6 ◇ q7) ◇ t) (apc4 q5 q6)).symm).trans ((h ((q6 ◇ q6) ◇ q5) q6 q7).symm)
  have apc7 : forall (q5 q6 q7:G), ((q6 ◇ q6) ◇ q5) = ((q6 ◇ q5) ◇ q5):=by
    intro q5 q6 q7
    exact ((apc6 q5 q6 q7).symm).trans ((apc6 q5 q6 q7).trans ((apc6 q5 q6 q5).symm))
  have apc8 : forall (q5 q6 q7:G), ((q6 ◇ q7) ◇ q5) = ((q6 ◇ q5) ◇ q5):=by
    intro q5 q6 q7
    exact (apc6 q5 q6 q7).trans (apc7 q5 q6 ((q6 ◇ q6) ◇ q5))
  have apc9 : forall (q3 q4:G), (((q4 ◇ q4) ◇ q4) ◇ q4) = q3:=by
    intro q3 q4
    exact ((apc8 q4 (q4 ◇ q4) (q4 ◇ q4)).symm).trans (((apc6 q4 (q4 ◇ q4) ((q4 ◇ q4) ◇ q3)).symm).trans (apc4 q3 q4))
  exact ((apc9 (x ◇ (x ◇ y)) (x ◇ (x ◇ y))).symm).trans (apc9 ((z ◇ (x ◇ x)) ◇ y) (x ◇ (x ◇ y)))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_21081_to_56565 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_21081_to_56565
