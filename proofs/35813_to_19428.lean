-- Equation35813 → Equation19428
-- Recorded verdict: true
-- Premise: x = ((y * (y * y)) * (z * w)) * x
-- Conclusion: x = (y * z) * ((z * z) * (z * x))
-- Original submission SHA-256: 86f7226a5c94ddc0856bb33be2fdc69c5b6687bc8db5496b57e3df3e9a2b4e70
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ (y ◇ y)) ◇ (z ◇ w)) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ z) ◇ ((z ◇ z) ◇ (z ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), ((q2 ◇ q0) ◇ q1) = q1:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ q1) ((h (q2 ◇ q0) q0 (q0 ◇ (q0 ◇ q0)) (q0 ◇ (q0 ◇ q0))).symm)).symm).trans ((h q1 (q0 ◇ (q0 ◇ q0)) q2 q0).symm)
  have apc1 : forall (q3 q4:G), (q3 ◇ q4) = q4:=by
    intro q3 q4
    exact ((congrArg (fun t => t ◇ q4) (apc0 q3 q3 q3)).symm).trans (apc0 q3 q4 (q3 ◇ q3))
  exact (calc
    x = x:=rfl
    _ = ((y ◇ z) ◇ ((z ◇ z) ◇ (z ◇ x))):=(((((congrArg (fun t => (y ◇ z) ◇ t) (congrArg (fun t => (z ◇ z) ◇ t) (apc1 z x))).trans (congrArg (fun t => (y ◇ z) ◇ t) (congrArg (fun t => t ◇ x) (apc1 z z)))).trans (congrArg (fun t => t ◇ (z ◇ x)) (apc1 y z))).trans (congrArg (fun t => z ◇ t) (apc1 z x))).trans (apc1 z x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_35813_to_19428 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_35813_to_19428
