-- Equation42601 → Equation43288
-- Recorded verdict: true
-- Premise: x ◇ x = y ◇ (z ◇ ((w ◇ w) ◇ w))
-- Conclusion: x ◇ x = x ◇ ((x ◇ y) ◇ (x ◇ x))
-- Original submission SHA-256: be185232c7fdd9d79e66774a6e9377b84695ca5b55d293d763f1dc02661f630d
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = y ◇ (z ◇ ((w ◇ w) ◇ w))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ x = x ◇ ((x ◇ y) ◇ (x ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  calc
    (x ◇ x) = (x ◇ ((x ◇ y) ◇ (x ◇ x))):=(h x x (x ◇ y) (x ◇ x)).trans (((((congrArg (fun t => x ◇ t) (congrArg (fun t => (x ◇ y) ◇ t) (h x x x x))).trans (congrArg (fun t => x ◇ t) (congrArg (fun t => (x ◇ y) ◇ t) ((h (x ◇ x) x x x).symm)))).trans (congrArg (fun t => x ◇ t) (congrArg (fun t => (x ◇ y) ◇ t) (congrArg (fun t => t ◇ (x ◇ x)) (h x x x x))))).trans (congrArg (fun t => x ◇ t) (congrArg (fun t => (x ◇ y) ◇ t) (congrArg (fun t => t ◇ (x ◇ x)) ((h (x ◇ x) x x x).symm))))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_42601_to_43288 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_42601_to_43288
