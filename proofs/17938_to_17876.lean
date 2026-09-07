-- Equation17938 → Equation17876
-- Recorded verdict: true
-- Premise: x = (x * y) * (x * ((z * w) * u))
-- Conclusion: x = (x * x) * (y * ((y * x) * y))
-- Original submission SHA-256: f8dac147dfa7765a5f326ebce62a4c8a52e36a3d9e947f243d444d7906744c5f
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (x ◇ y) ◇ (x ◇ ((z ◇ w) ◇ u))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (x ◇ x) ◇ (y ◇ ((y ◇ x) ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc1 : forall (q0 q1 q2:G), ((q0 ◇ q1) ◇ (q0 ◇ q2)) = q0:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => (q0 ◇ q1) ◇ t) (congrArg (fun t => q0 ◇ t) ((h q2 q0 q0 q0 q0).symm))).symm).trans ((h q0 q1 q2 q0 (q2 ◇ ((q0 ◇ q0) ◇ q0))).symm)
  have apc2 : forall (q3 q4 q5 q6 q2:G), (q3 ◇ ((q3 ◇ q4) ◇ ((q2 ◇ q6) ◇ q5))) = (q3 ◇ q4):=by
    intro q3 q4 q5 q6 q2
    exact ((congrArg (fun t => t ◇ ((q3 ◇ q4) ◇ ((q2 ◇ q6) ◇ q5))) ((h q3 q4 q3 q3 q3).symm)).symm).trans ((h (q3 ◇ q4) (q3 ◇ ((q3 ◇ q3) ◇ q3)) q2 q6 q5).symm)
  have apc3 : forall (q7 q8 q9:G), ((q9 ◇ q8) ◇ q7) = q9:=by
    intro q7 q8 q9
    exact (((apc1 q9 q8 q8).symm).trans (((congrArg (fun t => (q9 ◇ q8) ◇ t) ((h (q9 ◇ q8) q7 q7 q7 q7).symm)).symm).trans (apc2 (q9 ◇ q8) q7 ((q7 ◇ q7) ◇ q7) q8 q9))).symm
  exact (apc3 (y ◇ ((y ◇ x) ◇ y)) x x).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_17938_to_17876 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_17938_to_17876
