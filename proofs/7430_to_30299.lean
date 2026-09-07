-- Equation7430 → Equation30299
-- Recorded verdict: true
-- Premise: x = x * (y * ((y * (y * y)) * z))
-- Conclusion: x = (x * (y * ((z * z) * z))) * w
-- Original submission SHA-256: b1897bdb1af16e35035414ab0766dac7d14629231ea2c2e0b33e911aa411fea5
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = x ◇ (y ◇ ((y ◇ (y ◇ y)) ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (x ◇ (y ◇ ((z ◇ z) ◇ z))) ◇ w
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1:G), (q0 ◇ q1) = q0:=by
    intro q0 q1
    exact ((congrArg (fun t => q0 ◇ t) ((h q1 (q1 ◇ (q1 ◇ q1)) q0).symm)).symm).trans ((h q0 q1 (((q1 ◇ (q1 ◇ q1)) ◇ ((q1 ◇ (q1 ◇ q1)) ◇ (q1 ◇ (q1 ◇ q1)))) ◇ q0)).symm)
  exact ((apc0 x (y ◇ ((z ◇ z) ◇ z))).symm).trans ((apc0 (x ◇ (y ◇ ((z ◇ z) ◇ z))) w).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_7430_to_30299 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_7430_to_30299
