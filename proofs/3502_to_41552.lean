-- Equation3502 → Equation41552
-- Recorded verdict: true
-- Premise: x ◇ x = y ◇ ((z ◇ z) ◇ w)
-- Conclusion: x ◇ x = x ◇ (y ◇ (x ◇ (z ◇ z)))
-- Original submission SHA-256: 573eb1b44fd5dba5c967b4372ce89d797e64fcca8c91fbe1c3b9fbe144856c94
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = y ◇ ((z ◇ z) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = x ◇ (y ◇ (x ◇ (z ◇ z)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  calc
    (x ◇ x) = (x ◇ (y ◇ (x ◇ (z ◇ z)))):=(h x x x (x ◇ x)).trans (((((congrArg (fun t => x ◇ t) (congrArg (fun t => y ◇ t) (congrArg (fun t => x ◇ t) (h z x x x)))).trans (congrArg (fun t => x ◇ t) (congrArg (fun t => y ◇ t) (congrArg (fun t => x ◇ t) ((h (x ◇ x) x x x).symm))))).trans (congrArg (fun t => x ◇ t) (congrArg (fun t => y ◇ t) ((h (x ◇ x) x x (x ◇ x)).symm)))).trans (congrArg (fun t => x ◇ t) ((h (x ◇ x) y x (x ◇ x)).symm))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_3502_to_41552 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_3502_to_41552
