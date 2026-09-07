-- Equation41590 → Equation43473
-- Recorded verdict: true
-- Premise: x ◇ x = y ◇ (x ◇ (x ◇ (z ◇ w)))
-- Conclusion: x ◇ x = y ◇ ((z ◇ w) ◇ (z ◇ w))
-- Original submission SHA-256: dc86c8d925f6f1ba8d4d2be7d443dc8f8e875ce59997641567962b0faf11c606
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = y ◇ (x ◇ (x ◇ (z ◇ w)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = y ◇ ((z ◇ w) ◇ (z ◇ w))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  calc
    (x ◇ x) = (y ◇ ((z ◇ w) ◇ (z ◇ w))):=(((((h x y x (x ◇ x)).trans (congrArg (fun t => y ◇ t) ((h x x x x).symm))).trans (congrArg (fun t => y ◇ t) (h x (z ◇ w) x (x ◇ x)))).trans (congrArg (fun t => y ◇ t) (congrArg (fun t => (z ◇ w) ◇ t) ((h x x x x).symm)))).trans (congrArg (fun t => y ◇ t) (congrArg (fun t => (z ◇ w) ◇ t) (h x (z ◇ w) z w)))).trans ((((congrArg (fun t => y ◇ t) (h (z ◇ w) (z ◇ w) w w)).trans ((h (z ◇ w) y (z ◇ w) (w ◇ w)).symm)).trans (h (z ◇ w) y x (x ◇ (z ◇ w)))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_41590_to_43473 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_41590_to_43473
