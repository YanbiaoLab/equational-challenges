-- Equation13588 → Equation48010
-- Recorded verdict: true
-- Premise: x = x * ((y * ((y * z) * w)) * z)
-- Conclusion: x * y = (x * (z * w)) * (z * u)
-- Original submission SHA-256: 1186e2360a4080be1d977e6ddcd15eb36ec79ffcce45618ce968580d9f5ef059
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = x ◇ ((y ◇ ((y ◇ z) ◇ w)) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = (x ◇ (z ◇ w)) ◇ (z ◇ u)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1 q2 q3:G), (q2 ◇ (q3 ◇ ((q3 ◇ q1) ◇ q0))) = q2:=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => q2 ◇ t) (congrArg (fun t => t ◇ ((q3 ◇ q1) ◇ q0)) ((h q3 q3 q1 q0).symm))).symm).trans ((h q2 q3 ((q3 ◇ q1) ◇ q0) q1).symm)
  have apc1 : forall (q4 q5:G), (q4 ◇ q5) = q4:=by
    intro q4 q5
    exact ((congrArg (fun t => q4 ◇ t) (apc0 q4 q4 q5 (q5 ◇ q4))).symm).trans (apc0 (((q5 ◇ q4) ◇ q4) ◇ q4) q4 q4 q5)
  exact (calc
    (x ◇ y) = x:=apc1 x y
    _ = ((x ◇ (z ◇ w)) ◇ (z ◇ u)):=((((congrArg (fun t => t ◇ (z ◇ u)) (congrArg (fun t => x ◇ t) (apc1 z w))).trans (congrArg (fun t => t ◇ (z ◇ u)) (apc1 x z))).trans (congrArg (fun t => x ◇ t) (apc1 z u))).trans (apc1 x z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_13588_to_48010 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_13588_to_48010
