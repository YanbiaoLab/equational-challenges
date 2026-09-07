-- Equation13563 → Equation52066
-- Recorded verdict: true
-- Premise: x = x * ((y * ((y * x) * z)) * w)
-- Conclusion: x * x = ((x * (x * y)) * z) * z
-- Original submission SHA-256: 4af4c3e6a588d164ff4e1163d34a37066b91330ab47d2e81de2e1ce217ae6e36
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = x ◇ ((y ◇ ((y ◇ x) ◇ z)) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = ((x ◇ (x ◇ y)) ◇ z) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc2 : forall (q0 q1 q2:G), (q0 ◇ (q1 ◇ ((q1 ◇ q0) ◇ q2))) = q0:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q0 ◇ t) ((h (q1 ◇ ((q1 ◇ q0) ◇ q2)) q0 q0 q0).symm)).symm).trans ((h q0 q1 q2 ((q0 ◇ ((q0 ◇ (q1 ◇ ((q1 ◇ q0) ◇ q2))) ◇ q0)) ◇ q0)).symm)
  have apc4 : forall (q3 q4:G), (q3 ◇ q4) = q3:=by
    intro q3 q4
    exact ((congrArg (fun t => q3 ◇ t) (apc2 q4 (q4 ◇ q3) q3)).symm).trans (apc2 q3 q4 (((q4 ◇ q3) ◇ q4) ◇ q3))
  exact (calc
    (x ◇ x) = x:=apc4 x x
    _ = (((x ◇ (x ◇ y)) ◇ z) ◇ z):=((((congrArg (fun t => t ◇ z) (congrArg (fun t => t ◇ z) (congrArg (fun t => x ◇ t) (apc4 x y)))).trans (congrArg (fun t => t ◇ z) (congrArg (fun t => t ◇ z) (apc4 x x)))).trans (congrArg (fun t => t ◇ z) (apc4 x z))).trans (apc4 x z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_13563_to_52066 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_13563_to_52066
