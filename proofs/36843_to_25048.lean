-- Equation36843 → Equation25048
-- Recorded verdict: true
-- Premise: x = (((y * z) * x) * (w * u)) * x
-- Conclusion: x = (x * (y * (z * w))) * (y * x)
-- Original submission SHA-256: bcad869ce40f0af6ff93a0c28ecf0984b767904653b04499dbcee1c4be4f11be
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (((y ◇ z) ◇ x) ◇ (w ◇ u)) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (x ◇ (y ◇ (z ◇ w))) ◇ (y ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2:G), ((q2 ◇ (q1 ◇ q0)) ◇ q2) = q2:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ q2) (congrArg (fun t => t ◇ (q1 ◇ q0)) ((h q2 q0 q0 q0 q0).symm))).symm).trans ((h q2 ((q0 ◇ q0) ◇ q2) (q0 ◇ q0) q1 q0).symm)
  have apc1 : forall (q3 q4:G), ((q4 ◇ q3) ◇ q4) = q4:=by
    intro q3 q4
    exact ((congrArg (fun t => t ◇ q4) (congrArg (fun t => q4 ◇ t) (apc0 q3 q3 q3))).symm).trans (apc0 q3 (q3 ◇ (q3 ◇ q3)) q4)
  have apc2 : forall (q5 q6 q7:G), ((q6 ◇ q5) ◇ q7) = q7:=by
    intro q5 q6 q7
    exact ((congrArg (fun t => t ◇ q7) (apc1 q7 (q6 ◇ q5))).symm).trans ((h q7 q6 q5 q6 q5).symm)
  have apc3 : forall (q8 q9:G), (q8 ◇ q9) = q9:=by
    intro q8 q9
    exact ((congrArg (fun t => t ◇ q9) (apc2 q8 q8 q8)).symm).trans (apc2 q8 (q8 ◇ q8) q9)
  exact ((apc3 y x).symm).trans ((apc3 (x ◇ (y ◇ (z ◇ w))) (y ◇ x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_36843_to_25048 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_36843_to_25048
