-- Equation10986 → Equation35515
-- Recorded verdict: true
-- Premise: x = x * ((y * (z * y)) * (z * y))
-- Conclusion: x = ((x * (y * y)) * (z * w)) * u
-- Original submission SHA-256: fca3a989a23cdc8718fd98c242186bcd986d66be804ee798d898806582b6f082
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = x ◇ ((y ◇ (z ◇ y)) ◇ (z ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = ((x ◇ (y ◇ y)) ◇ (z ◇ w)) ◇ u
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1 q2:G), (q2 ◇ ((q1 ◇ q0) ◇ ((q0 ◇ (q1 ◇ q0)) ◇ (q1 ◇ q0)))) = q2:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q2 ◇ t) ((h ((q1 ◇ q0) ◇ ((q0 ◇ (q1 ◇ q0)) ◇ (q1 ◇ q0))) q0 q1).symm)).symm).trans ((h q2 (q1 ◇ q0) (q0 ◇ (q1 ◇ q0))).symm)
  have apc1 : forall (q3 q4 q5:G), (q5 ◇ (q4 ◇ q3)) = q5:=by
    intro q3 q4 q5
    exact ((congrArg (fun t => q5 ◇ t) ((h (q4 ◇ q3) q3 q4).symm)).symm).trans (apc0 q3 q4 q5)
  have apc2 : forall (q6 q7:G), (q7 ◇ q6) = q7:=by
    intro q6 q7
    exact ((congrArg (fun t => q7 ◇ t) (apc1 q6 q6 q6)).symm).trans (apc1 (q6 ◇ q6) q6 q7)
  exact (calc
    x = x:=rfl
    _ = (((x ◇ (y ◇ y)) ◇ (z ◇ w)) ◇ u):=(((((congrArg (fun t => t ◇ u) (congrArg (fun t => t ◇ (z ◇ w)) (congrArg (fun t => x ◇ t) (apc2 y y)))).trans (congrArg (fun t => t ◇ u) (congrArg (fun t => t ◇ (z ◇ w)) (apc2 y x)))).trans (congrArg (fun t => t ◇ u) (congrArg (fun t => x ◇ t) (apc2 w z)))).trans (congrArg (fun t => t ◇ u) (apc2 z x))).trans (apc2 u x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_10986_to_35515 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_10986_to_35515
