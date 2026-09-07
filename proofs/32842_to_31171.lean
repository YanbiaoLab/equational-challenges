-- Equation32842 → Equation31171
-- Recorded verdict: true
-- Premise: x = (x * (((y * x) * z) * z)) * w
-- Conclusion: x = (x * ((y * z) * (z * y))) * z
-- Original submission SHA-256: 1f170428f54a2c2446bed93fbc5ce1b67a78ce037b9c977b23672a94b603e678
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (x ◇ (((y ◇ x) ◇ z) ◇ z)) ◇ w
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ ((y ◇ z) ◇ (z ◇ y))) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3:G), ((q2 ◇ ((q0 ◇ q3) ◇ q3)) ◇ q1) = q2:=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ q1) (congrArg (fun t => q2 ◇ t) (congrArg (fun t => t ◇ q3) (congrArg (fun t => t ◇ q3) ((h q0 q0 q0 q2).symm))))).symm).trans ((h q2 (q0 ◇ (((q0 ◇ q0) ◇ q0) ◇ q0)) q3 q1).symm)
  have apc2 : forall (q4 q5 q6:G), ((q6 ◇ q4) ◇ q5) = q6:=by
    intro q4 q5 q6
    exact ((congrArg (fun t => t ◇ q5) (congrArg (fun t => q6 ◇ t) (apc0 q4 ((q4 ◇ q4) ◇ q4) q4 q4))).symm).trans (apc0 q4 q5 q6 ((q4 ◇ q4) ◇ q4))
  exact (calc
    x = x:=rfl
    _ = ((x ◇ ((y ◇ z) ◇ (z ◇ y))) ◇ z):=((congrArg (fun t => t ◇ z) (congrArg (fun t => x ◇ t) (apc2 z (z ◇ y) y))).trans (apc2 y z x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_32842_to_31171 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_32842_to_31171
