-- Equation34992 → Equation17855
-- Recorded verdict: true
-- Premise: x = ((y * y) * ((z * w) * x)) * x
-- Conclusion: x = (x * x) * (x * ((y * x) * x))
-- Original submission SHA-256: dd72e84fc0c7d27892a79b407ba6c4aa269912f454dcf71d4fc0b577a43c3e62
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ y) ◇ ((z ◇ w) ◇ x)) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (x ◇ x) ◇ (x ◇ ((y ◇ x) ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (q0 q1 q2:G), (((q2 ◇ q0) ◇ q1) ◇ q1) = q1:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ q1) ((h ((q2 ◇ q0) ◇ q1) ((q2 ◇ q0) ◇ q1) (q2 ◇ q0) q1).symm)).symm).trans ((h q1 (((q2 ◇ q0) ◇ q1) ◇ ((q2 ◇ q0) ◇ q1)) q2 q0).symm)
  have apc1 : forall (q3 q4:G), ((q3 ◇ q4) ◇ q4) = q4:=by
    intro q3 q4
    exact ((congrArg (fun t => t ◇ q4) (congrArg (fun t => t ◇ q4) (apc0 q3 q3 q3))).symm).trans (apc0 q3 q4 ((q3 ◇ q3) ◇ q3))
  have apc2 : forall (q4:G), (q4 ◇ q4) = q4:=by
    intro q4
    exact ((congrArg (fun t => t ◇ q4) (apc0 q4 q4 q4)).symm).trans (apc0 q4 q4 (q4 ◇ q4))
  exact (calc
    x = x:=rfl
    _ = ((x ◇ x) ◇ (x ◇ ((y ◇ x) ◇ x))):=((((congrArg (fun t => (x ◇ x) ◇ t) (congrArg (fun t => x ◇ t) (apc1 y x))).trans (congrArg (fun t => t ◇ (x ◇ x)) (apc2 x))).trans (congrArg (fun t => x ◇ t) (apc2 x))).trans (apc2 x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_34992_to_17855 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_34992_to_17855
