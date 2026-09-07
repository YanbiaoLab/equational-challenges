-- Equation20951 → Equation6583
-- Recorded verdict: true
-- Premise: x = (y * y) * (((z * z) * z) * x)
-- Conclusion: x = x * (y * ((z * x) * (z * x)))
-- Original submission SHA-256: 32d1c462b5486c8b7b0866e6ea25de6fc55e7eb1520cffdc298c3ccc8151385b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ y) ◇ (((z ◇ z) ◇ z) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = x ◇ (y ◇ ((z ◇ x) ◇ (z ◇ x)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), ((q2 ◇ q2) ◇ (q0 ◇ q1)) = q1:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => (q2 ◇ q2) ◇ t) (congrArg (fun t => t ◇ q1) ((h q0 (((q0 ◇ q0) ◇ q0) ◇ q0) q0).symm))).symm).trans ((h q1 q2 (((q0 ◇ q0) ◇ q0) ◇ q0)).symm)
  have apc1 : forall (q3 q4 q5:G), (q3 ◇ (q4 ◇ q5)) = q5:=by
    intro q3 q4 q5
    exact ((congrArg (fun t => t ◇ (q4 ◇ q5)) (apc0 q3 q3 q3)).symm).trans (apc0 q4 q5 (q3 ◇ q3))
  exact (calc
    x = x:=rfl
    _ = (x ◇ (y ◇ ((z ◇ x) ◇ (z ◇ x)))):=((congrArg (fun t => x ◇ t) (congrArg (fun t => y ◇ t) (apc1 (z ◇ x) z x))).trans (apc1 x y x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_20951_to_6583 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_20951_to_6583
