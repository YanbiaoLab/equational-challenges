-- Equation14175 → Equation20512
-- Recorded verdict: true
-- Premise: x = y * ((z * ((z * w) * x)) * x)
-- Conclusion: x = (x * x) * (((y * y) * z) * x)
-- Original submission SHA-256: 9466c1bda3c04e012bd5995e044f0d01197f2f9eb5ad5b4b7ca7373182825081
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ ((z ◇ ((z ◇ w) ◇ x)) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ x) ◇ (((y ◇ y) ◇ z) ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1:G), (q1 ◇ (q0 ◇ q0)) = q0:=by
    intro q0 q1
    exact ((congrArg (fun t => q1 ◇ t) (congrArg (fun t => t ◇ q0) ((h q0 q0 q0 q0).symm))).symm).trans ((h q0 q1 q0 ((q0 ◇ q0) ◇ q0)).symm)
  have apc2 : forall (q2 q3:G), (q3 ◇ q2) = (q2 ◇ q2):=by
    intro q2 q3
    exact ((congrArg (fun t => q3 ◇ t) (apc0 q2 (q2 ◇ q2))).symm).trans (apc0 (q2 ◇ q2) q3)
  exact (calc
    x = x:=rfl
    _ = ((x ◇ x) ◇ (((y ◇ y) ◇ z) ◇ x)):=(((congrArg (fun t => (x ◇ x) ◇ t) (congrArg (fun t => t ◇ x) (apc2 z (y ◇ y)))).trans (congrArg (fun t => (x ◇ x) ◇ t) (apc2 x (z ◇ z)))).trans (apc0 x (x ◇ x))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_14175_to_20512 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_14175_to_20512
