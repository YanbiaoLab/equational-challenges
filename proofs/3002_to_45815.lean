-- Equation3002 → Equation45815
-- Recorded verdict: true
-- Premise: x = ((y * (z * y)) * w) * x
-- Conclusion: x * y = z * (((w * y) * w) * y)
-- Original submission SHA-256: 5339e2af788e9f1708bb33ccbb09bd23b3af920b58fb089ea4f49378129e3b90
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ (z ◇ y)) ◇ w) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ (((w ◇ y) ◇ w) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1:G), (q0 ◇ q1) = q1:=by
    intro q0 q1
    exact ((congrArg (fun t => t ◇ q1) ((h q0 q0 q0 (q0 ◇ (q0 ◇ (q0 ◇ q0)))).symm)).symm).trans ((h q1 (q0 ◇ (q0 ◇ q0)) q0 q0).symm)
  exact (calc
    (x ◇ y) = y:=apc0 x y
    _ = (z ◇ (((w ◇ y) ◇ w) ◇ y)):=((((congrArg (fun t => z ◇ t) (congrArg (fun t => t ◇ y) (congrArg (fun t => t ◇ w) (apc0 w y)))).trans (congrArg (fun t => z ◇ t) (congrArg (fun t => t ◇ y) (apc0 y w)))).trans (congrArg (fun t => z ◇ t) (apc0 w y))).trans (apc0 z y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_3002_to_45815 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_3002_to_45815
