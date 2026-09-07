-- Equation320 → Equation41562
-- Recorded verdict: true
-- Premise: x ◇ x = y ◇ (z ◇ z)
-- Conclusion: x ◇ x = x ◇ (y ◇ (y ◇ (z ◇ z)))
-- Original submission SHA-256: d5daba8a70b46c95502bf35e6616b32dde37f39cd34ec89a97aa178bdbc9bd3b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ (z ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = x ◇ (y ◇ (y ◇ (z ◇ z)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  calc
    (x ◇ x) = (x ◇ (y ◇ (y ◇ (z ◇ z)))):=((h x x y).trans (congrArg (fun t => x ◇ t) (h y y y))).trans ((congrArg (fun t => x ◇ t) (congrArg (fun t => y ◇ t) ((h y y z).symm))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_320_to_41562 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_320_to_41562
