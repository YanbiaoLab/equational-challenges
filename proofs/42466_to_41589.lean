-- Equation42466 → Equation41589
-- Recorded verdict: true
-- Premise: x ◇ x = y ◇ (x ◇ ((x ◇ z) ◇ z))
-- Conclusion: x ◇ x = y ◇ (x ◇ (x ◇ (z ◇ z)))
-- Original submission SHA-256: 95e516d17774923dd91198b37e6b3cf487376d230230e2aa56369f4bd349f768
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ (x ◇ ((x ◇ z) ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ (x ◇ (x ◇ (z ◇ z)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  have aux : forall (x y z:G), (y ◇ (x ◇ (z ◇ z))) = (x ◇ x):=by
    intro x y z
    exact ((congrArg (fun t => y ◇ t) (congrArg (fun t => x ◇ t) (h z (z ◇ z) x))).trans (congrArg (fun t => y ◇ t) (congrArg (fun t => x ◇ t) (congrArg (fun t => t ◇ (z ◇ ((z ◇ x) ◇ x))) (h z x x))))).trans ((h x y (z ◇ ((z ◇ x) ◇ x))).symm)
  intro x y z
  calc
    (x ◇ x) = (y ◇ (x ◇ (x ◇ (z ◇ z)))):=(((aux x y (z ◇ z)).symm).trans (congrArg (fun t => y ◇ t) (congrArg (fun t => x ◇ t) ((aux (z ◇ z) x z).symm)))).trans (((congrArg (fun t => y ◇ t) (aux x x z)).trans (congrArg (fun t => y ◇ t) ((aux x x (z ◇ z)).symm))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_42466_to_41589 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_42466_to_41589
