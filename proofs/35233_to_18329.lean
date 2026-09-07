-- Equation35233 → Equation18329
-- Recorded verdict: true
-- Premise: x = ((y * z) * ((z * w) * z)) * x
-- Conclusion: x = (y * y) * (z * ((w * x) * x))
-- Original submission SHA-256: dac6ed863eaa378019727f719256f03cb192049d432249fbfb50970351da47df
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ z) ◇ ((z ◇ w) ◇ z)) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ y) ◇ (z ◇ ((w ◇ x) ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2:G), ((q2 ◇ ((q2 ◇ q0) ◇ q2)) ◇ q1) = q1:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ q1) (congrArg (fun t => t ◇ ((q2 ◇ q0) ◇ q2)) ((h q2 q0 q0 q0).symm))).symm).trans ((h q1 ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) q2 q0).symm)
  have apc1 : forall (q3 q4:G), ((q4 ◇ q4) ◇ q3) = q3:=by
    intro q3 q4
    exact ((congrArg (fun t => t ◇ q3) (congrArg (fun t => q4 ◇ t) (apc0 q3 q4 q4))).symm).trans (apc0 ((q4 ◇ q3) ◇ q4) q3 q4)
  have apc3 : forall (q5 q6 q7:G), (((q7 ◇ q5) ◇ q7) ◇ q6) = q6:=by
    intro q5 q6 q7
    exact ((congrArg (fun t => t ◇ q6) (apc1 ((q7 ◇ q5) ◇ q7) q7)).symm).trans ((h q6 q7 q7 q5).symm)
  have apc6 : forall (q8 q9:G), (q8 ◇ q9) = q9:=by
    intro q8 q9
    exact ((congrArg (fun t => t ◇ q9) (apc1 q8 q8)).symm).trans (apc3 q8 q9 q8)
  exact (calc
    x = x:=rfl
    _ = ((y ◇ y) ◇ (z ◇ ((w ◇ x) ◇ x))):=(((((congrArg (fun t => (y ◇ y) ◇ t) (congrArg (fun t => z ◇ t) (congrArg (fun t => t ◇ x) (apc6 w x)))).trans (congrArg (fun t => (y ◇ y) ◇ t) (congrArg (fun t => z ◇ t) (apc6 x x)))).trans (congrArg (fun t => t ◇ (z ◇ x)) (apc6 y y))).trans (congrArg (fun t => y ◇ t) (apc6 z x))).trans (apc6 y x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_35233_to_18329 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_35233_to_18329
