-- Equation31145 → Equation17171
-- Recorded verdict: true
-- Premise: x = (x * ((y * z) * (x * w))) * z
-- Conclusion: x = (x * y) * (z * (w * (u * y)))
-- Original submission SHA-256: a08b97d153565840ee1fca3530a91ffdf215358af4007c9395bc0efa7f8ab7f5
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (x ◇ ((y ◇ z) ◇ (x ◇ w))) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (x ◇ y) ◇ (z ◇ (w ◇ (u ◇ y)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1 q2 q3 q4:G), ((q3 ◇ q4) ◇ ((q1 ◇ (q3 ◇ q2)) ◇ (q4 ◇ q0))) = q3:=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => t ◇ ((q1 ◇ (q3 ◇ q2)) ◇ (q4 ◇ q0))) (congrArg (fun t => q3 ◇ t) ((h q4 q1 (q3 ◇ q2) q0).symm))).symm).trans ((h q3 q4 ((q1 ◇ (q3 ◇ q2)) ◇ (q4 ◇ q0)) q2).symm)
  have apc1 : forall (q5 q6 q7 q8:G), ((q7 ◇ q8) ◇ (q5 ◇ (q8 ◇ q6))) = q7:=by
    intro q5 q6 q7 q8
    exact ((congrArg (fun t => (q7 ◇ q8) ◇ t) (congrArg (fun t => t ◇ (q8 ◇ q6)) ((h q5 q5 (q7 ◇ q5) q5).symm))).symm).trans (apc0 q6 (q5 ◇ ((q5 ◇ (q7 ◇ q5)) ◇ (q5 ◇ q5))) q5 q7 q8)
  have apc2 : forall (q9 q10 q11:G), ((q10 ◇ q11) ◇ q9) = q10:=by
    intro q9 q10 q11
    exact ((congrArg (fun t => (q10 ◇ q11) ◇ t) (apc1 q11 q9 q9 q9)).symm).trans (apc1 (q9 ◇ q9) (q9 ◇ q9) q10 q11)
  exact (calc
    x = x:=rfl
    _ = ((x ◇ y) ◇ (z ◇ (w ◇ (u ◇ y)))):=(apc2 (z ◇ (w ◇ (u ◇ y))) x y).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_31145_to_17171 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_31145_to_17171
