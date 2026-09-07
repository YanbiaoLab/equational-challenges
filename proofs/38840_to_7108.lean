-- Equation38840 → Equation7108
-- Recorded verdict: true
-- Premise: x = ((y * ((z * w) * w)) * y) * x
-- Conclusion: x = y * (z * ((z * x) * (x * x)))
-- Original submission SHA-256: b32753905fe12be3a8f0e92bd1e738ac222a60e29dfdcccbdf80a5cb1929e5dc
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ ((z ◇ w) ◇ w)) ◇ y) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (z ◇ ((z ◇ x) ◇ (x ◇ x)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), (((q2 ◇ q0) ◇ q2) ◇ q1) = q1:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ q1) (congrArg (fun t => t ◇ q2) (congrArg (fun t => q2 ◇ t) ((h q0 q0 q0 q0).symm)))).symm).trans ((h q1 q2 (q0 ◇ ((q0 ◇ q0) ◇ q0)) q0).symm)
  have apc1 : forall (q3 q4 q5:G), ((q4 ◇ q3) ◇ q5) = q5:=by
    intro q3 q4 q5
    exact ((congrArg (fun t => t ◇ q5) (apc0 q3 (q4 ◇ q3) q4)).symm).trans (apc0 q4 q5 (q4 ◇ q3))
  have apc2 : forall (q0 q1 q2 q3 q4 q5:G), (q2 ◇ q1) = q1:=by
    intro q0 q1 q2 q3 q4 q5
    exact ((congrArg (fun t => t ◇ q1) (apc1 q0 q2 q2)).symm).trans (apc0 q0 q1 q2)
  exact (calc
    x = x:=rfl
    _ = (y ◇ (z ◇ ((z ◇ x) ◇ (x ◇ x)))):=(((((congrArg (fun t => y ◇ t) (congrArg (fun t => z ◇ t) (congrArg (fun t => (z ◇ x) ◇ t) (apc2 (x ◇ x) x x (x ◇ x) (x ◇ x) (x ◇ x))))).trans (congrArg (fun t => y ◇ t) (congrArg (fun t => z ◇ t) (congrArg (fun t => t ◇ x) (apc2 (z ◇ x) x z (z ◇ x) (z ◇ x) (z ◇ x)))))).trans (congrArg (fun t => y ◇ t) (congrArg (fun t => z ◇ t) (apc2 (x ◇ x) x x (x ◇ x) (x ◇ x) (x ◇ x))))).trans (congrArg (fun t => y ◇ t) (apc2 (z ◇ x) x z (z ◇ x) (z ◇ x) (z ◇ x)))).trans (apc2 (y ◇ x) x y (y ◇ x) (y ◇ x) (y ◇ x))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_38840_to_7108 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_38840_to_7108
