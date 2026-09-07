-- Equation38850 → Equation53854
-- Recorded verdict: true
-- Premise: x = ((y * ((z * w) * w)) * w) * x
-- Conclusion: x * (x * x) = y * (z * (w * x))
-- Original submission SHA-256: 8029eccce8fca2975b81200d0140aec7052b2291a48c7b96515bd156a122b9ee
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ ((z ◇ w) ◇ w)) ◇ w) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (x ◇ x) = y ◇ (z ◇ (w ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1:G), (q0 ◇ q1) = q1:=by
    intro q0 q1
    exact ((congrArg (fun t => t ◇ q1) ((h q0 q0 q0 ((q0 ◇ q0) ◇ q0)).symm)).symm).trans ((h q1 (q0 ◇ ((q0 ◇ ((q0 ◇ q0) ◇ q0)) ◇ ((q0 ◇ q0) ◇ q0))) q0 q0).symm)
  exact (calc
    (x ◇ (x ◇ x)) = x:=(congrArg (fun t => x ◇ t) (apc0 x x)).trans (apc0 x x)
    _ = (y ◇ (z ◇ (w ◇ x))):=(((congrArg (fun t => y ◇ t) (congrArg (fun t => z ◇ t) (apc0 w x))).trans (congrArg (fun t => y ◇ t) (apc0 z x))).trans (apc0 y x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_38850_to_53854 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_38850_to_53854
