-- Equation30799 → Equation40166
-- Recorded verdict: true
-- Premise: x = (y * (z * ((z * x) * w))) * x
-- Conclusion: x = (((y * (y * y)) * x) * x) * x
-- Original submission SHA-256: 571c241313874253380bc1bedb279ee2cef4bfe2d112f1c1a8593bcd1b9c7b0d
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ (z ◇ ((z ◇ x) ◇ w))) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (((y ◇ (y ◇ y)) ◇ x) ◇ x) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (q0 q1 q2:G), ((q2 ◇ ((q2 ◇ q1) ◇ q0)) ◇ q1) = q1:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ q1) ((h (q2 ◇ ((q2 ◇ q1) ◇ q0)) q0 q0 q0).symm)).symm).trans ((h q1 (q0 ◇ (q0 ◇ ((q0 ◇ (q2 ◇ ((q2 ◇ q1) ◇ q0))) ◇ q0))) q2 q0).symm)
  have apc1 : forall (q3 q4 q5 q6:G), (((q4 ◇ ((q4 ◇ q6) ◇ q3)) ◇ (q6 ◇ q5)) ◇ q6) = q6:=by
    intro q3 q4 q5 q6
    exact ((congrArg (fun t => t ◇ q6) (congrArg (fun t => (q4 ◇ ((q4 ◇ q6) ◇ q3)) ◇ t) (congrArg (fun t => t ◇ q5) (apc0 q3 q6 q4)))).symm).trans (apc0 q5 q6 (q4 ◇ ((q4 ◇ q6) ◇ q3)))
  have apc2 : forall (q7 q8:G), ((q8 ◇ q7) ◇ q8) = q8:=by
    intro q7 q8
    exact ((congrArg (fun t => t ◇ q8) ((h (q8 ◇ q7) q7 (q7 ◇ q8) q7).symm)).symm).trans (apc1 (((q7 ◇ q8) ◇ (q8 ◇ q7)) ◇ q7) q7 q7 q8)
  have apc6 : forall (q9 q10 q11:G), ((q11 ◇ (q9 ◇ q9)) ◇ q10) = q10:=by
    intro q9 q10 q11
    exact ((congrArg (fun t => t ◇ q10) (congrArg (fun t => q11 ◇ t) (congrArg (fun t => q9 ◇ t) (apc2 q10 q9)))).symm).trans ((h q10 q11 q9 q9).symm)
  exact (calc
    x = x:=rfl
    _ = ((((y ◇ (y ◇ y)) ◇ x) ◇ x) ◇ x):=((congrArg (fun t => t ◇ x) (congrArg (fun t => t ◇ x) (apc6 y x y))).trans (apc2 x x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_30799_to_40166 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_30799_to_40166
