-- Equation26439 → Equation31873
-- Recorded verdict: true
-- Premise: x = (y ◇ ((z ◇ z) ◇ z)) ◇ (x ◇ w)
-- Conclusion: x = (y ◇ ((z ◇ w) ◇ (u ◇ u))) ◇ u
-- Original submission SHA-256: ad5c44ff0c06eb7d51f8dd8eb5a18326c9b9766d8c76286eea346177a1831b48
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ ((z ◇ z) ◇ z)) ◇ (x ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (y ◇ ((z ◇ w) ◇ (u ◇ u))) ◇ u
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1 q2:G), ((q2 ◇ q2) ◇ (q1 ◇ q0)) = q1:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ (q1 ◇ q0)) ((h (q2 ◇ q2) q0 q0 q2).symm)).symm).trans ((h q1 (q0 ◇ ((q0 ◇ q0) ◇ q0)) q2 q0).symm)
  have apc2 : forall (q3 q4 q5 q6:G), ((q5 ◇ ((q6 ◇ q6) ◇ q6)) ◇ q3) = (q4 ◇ q4):=by
    intro q3 q4 q5 q6
    exact ((congrArg (fun t => (q5 ◇ ((q6 ◇ q6) ◇ q6)) ◇ t) (apc0 q3 q3 q4)).symm).trans ((h (q4 ◇ q4) q5 q6 (q3 ◇ q3)).symm)
  have apc3 : forall (q7 q8 q9 q10:G), ((q8 ◇ ((q9 ◇ q9) ◇ q9)) ◇ q7) = q10:=by
    intro q7 q8 q9 q10
    exact (apc2 q7 (q10 ◇ ((q7 ◇ q7) ◇ q7)) q8 q9).trans ((h q10 q10 q7 ((q7 ◇ q7) ◇ q7)).symm)
  have apc6 : forall (q11 q12 q13 q14:G), ((q13 ◇ q11) ◇ q12) = q14:=by
    intro q11 q12 q13 q14
    exact ((congrArg (fun t => t ◇ q12) (congrArg (fun t => q13 ◇ t) (apc3 ((q11 ◇ q11) ◇ q11) ((q11 ◇ q11) ◇ q11) q11 q11))).symm).trans (apc3 q12 q13 ((q11 ◇ q11) ◇ q11) q14)
  exact ((apc6 x x x x).symm).trans ((apc6 ((z ◇ w) ◇ (u ◇ u)) u y ((x ◇ x) ◇ x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_26439_to_31873 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_26439_to_31873
