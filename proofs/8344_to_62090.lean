-- Equation8344 → Equation62090
-- Recorded verdict: true
-- Premise: x = x * (y * (((z * x) * w) * w))
-- Conclusion: (x * y) * y = ((x * z) * w) * u
-- Original submission SHA-256: 356125a201df4408e08bf142aff4e8602f6a1b60035402d341e59ba09b470e97
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = x ◇ (y ◇ (((z ◇ x) ◇ w) ◇ w))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), (x ◇ y) ◇ y = ((x ◇ z) ◇ w) ◇ u
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1:G), (q0 ◇ q1) = q0:=by
    intro q0 q1
    exact ((congrArg (fun t => q0 ◇ t) ((h q1 ((q0 ◇ q0) ◇ (((q0 ◇ q1) ◇ q0) ◇ q0)) q0 q0).symm)).symm).trans ((h q0 q1 q0 (((q0 ◇ q1) ◇ q0) ◇ q0)).symm)
  exact (calc
    ((x ◇ y) ◇ y) = x:=(congrArg (fun t => t ◇ y) (apc0 x y)).trans (apc0 x y)
    _ = (((x ◇ z) ◇ w) ◇ u):=(((congrArg (fun t => t ◇ u) (congrArg (fun t => t ◇ w) (apc0 x z))).trans (congrArg (fun t => t ◇ u) (apc0 x w))).trans (apc0 x u)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_8344_to_62090 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_8344_to_62090
