-- Equation1643 → Equation32006
-- Recorded verdict: true
-- Premise: x = (x * x) * ((y * z) * w)
-- Conclusion: x = (x * ((y * (y * z)) * w)) * w
-- Original submission SHA-256: 8ebe97f8b5a1d208a024588eb38305561fff40d2888e44edc8802bde523e0462
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (x ◇ x) ◇ ((y ◇ z) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (x ◇ ((y ◇ (y ◇ z)) ◇ w)) ◇ w
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1:G), ((q0 ◇ q0) ◇ q1) = q0:=by
    intro q0 q1
    exact ((congrArg (fun t => (q0 ◇ q0) ◇ t) ((h q1 q0 q0 q0).symm)).symm).trans ((h q0 q1 q1 ((q0 ◇ q0) ◇ q0)).symm)
  have apc1 : forall (q2 q3:G), (q2 ◇ q3) = (q2 ◇ q2):=by
    intro q2 q3
    exact ((congrArg (fun t => t ◇ q3) (apc0 q2 (q2 ◇ q2))).symm).trans (apc0 (q2 ◇ q2) q3)
  exact (calc
    x = x:=rfl
    _ = ((x ◇ ((y ◇ (y ◇ z)) ◇ w)) ◇ w):=(((((congrArg (fun t => t ◇ w) (congrArg (fun t => x ◇ t) (congrArg (fun t => t ◇ w) (congrArg (fun t => y ◇ t) (apc1 y z))))).trans (congrArg (fun t => t ◇ w) (congrArg (fun t => x ◇ t) (congrArg (fun t => t ◇ w) (apc1 y (y ◇ y)))))).trans (congrArg (fun t => t ◇ w) (congrArg (fun t => x ◇ t) (apc0 y w)))).trans (congrArg (fun t => t ◇ w) (apc1 x y))).trans (apc0 x w)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_1643_to_32006 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_1643_to_32006
