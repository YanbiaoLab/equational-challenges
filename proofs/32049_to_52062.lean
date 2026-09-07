-- Equation32049 → Equation52062
-- Recorded verdict: true
-- Premise: x = (x * ((y * (z * z)) * y)) * w
-- Conclusion: x * x = ((x * (x * y)) * y) * y
-- Original submission SHA-256: 755d5dfbae7a8f3addff9d3822e6a3bf9afd8b0b1657ca808be1b0dfdd713a4a
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (x ◇ ((y ◇ (z ◇ z)) ◇ y)) ◇ w
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ x = ((x ◇ (x ◇ y)) ◇ y) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (q0 q1 q2 q3:G), ((q2 ◇ ((q3 ◇ q0) ◇ q3)) ◇ q1) = q2:=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ q1) (congrArg (fun t => q2 ◇ t) (congrArg (fun t => t ◇ q3) (congrArg (fun t => q3 ◇ t) ((h q0 q0 q0 (q0 ◇ ((q0 ◇ (q0 ◇ q0)) ◇ q0))).symm))))).symm).trans ((h q2 q3 (q0 ◇ ((q0 ◇ (q0 ◇ q0)) ◇ q0)) q1).symm)
  have apc1 : forall (q4 q5 q6:G), ((q5 ◇ q6) ◇ q4) = q5:=by
    intro q4 q5 q6
    exact ((congrArg (fun t => t ◇ q4) (congrArg (fun t => q5 ◇ t) (apc0 q4 q6 q6 q4))).symm).trans (apc0 ((q4 ◇ q4) ◇ q4) q4 q5 q6)
  have apc2 : forall (q7 q8 q9:G), (q7 ◇ q9) = (q7 ◇ q8):=by
    intro q7 q8 q9
    exact ((congrArg (fun t => t ◇ q9) (apc1 q7 q7 q8)).symm).trans (apc1 q9 (q7 ◇ q8) q7)
  have apc3 : forall (q7 q8 q9:G), (q7 ◇ q8) = (q7 ◇ q7):=by
    intro q7 q8 q9
    exact ((apc2 q7 q8 q9).symm).trans (apc2 q7 q7 q9)
  have apc4 : forall (q4 q5 q6 q7 q8 q9:G), ((q5 ◇ q5) ◇ q4) = q5:=by
    intro q4 q5 q6 q7 q8 q9
    exact ((congrArg (fun t => t ◇ q4) (apc3 q5 q6 (q5 ◇ q6))).symm).trans (apc1 q4 q5 q6)
  exact (calc
    (x ◇ x) = (x ◇ x):=rfl
    _ = (((x ◇ (x ◇ y)) ◇ y) ◇ y):=((((congrArg (fun t => t ◇ y) (congrArg (fun t => t ◇ y) (congrArg (fun t => x ◇ t) (apc3 x y (x ◇ y))))).trans (congrArg (fun t => t ◇ y) (congrArg (fun t => t ◇ y) (apc3 x (x ◇ x) (x ◇ (x ◇ x)))))).trans (congrArg (fun t => t ◇ y) (apc4 y x ((x ◇ x) ◇ y) ((x ◇ x) ◇ y) ((x ◇ x) ◇ y) ((x ◇ x) ◇ y)))).trans (apc3 x y (x ◇ y))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_32049_to_52062 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_32049_to_52062
