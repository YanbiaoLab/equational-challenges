-- Equation24378 → Equation40624
-- Recorded verdict: true
-- Premise: x = ((y ◇ y) ◇ x) ◇ ((z ◇ w) ◇ w)
-- Conclusion: x = (((y ◇ (z ◇ w)) ◇ u) ◇ y) ◇ w
-- Original submission SHA-256: 12c2734e87177e224bdce8d7f94404b9cdb8d23774122dc6196688eb17a9bc2f
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ y) ◇ x) ◇ ((z ◇ w) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (((y ◇ (z ◇ w)) ◇ u) ◇ y) ◇ w
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc1 : forall (q0 q1 q2 q3 q4:G), (((q4 ◇ q4) ◇ q3) ◇ (q1 ◇ ((q2 ◇ q0) ◇ q0))) = q3:=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => ((q4 ◇ q4) ◇ q3) ◇ t) (congrArg (fun t => t ◇ ((q2 ◇ q0) ◇ q0)) ((h q1 q0 q2 q0).symm))).symm).trans ((h q3 q4 ((q0 ◇ q0) ◇ q1) ((q2 ◇ q0) ◇ q0)).symm)
  have apc2 : forall (q5 q6 q7:G), (((q7 ◇ q7) ◇ q6) ◇ q5) = q6:=by
    intro q5 q6 q7
    exact ((congrArg (fun t => ((q7 ◇ q7) ◇ q6) ◇ t) ((h q5 q5 q5 q5).symm)).symm).trans (apc1 q5 ((q5 ◇ q5) ◇ q5) q5 q6 q7)
  have apc3 : forall (q8 q9 q10:G), ((q8 ◇ q8) ◇ q9) = q10:=by
    intro q8 q9 q10
    exact ((congrArg (fun t => t ◇ q9) (apc2 q10 (q8 ◇ q8) q8)).symm).trans (apc2 q9 q10 (q8 ◇ q8))
  exact ((apc3 x ((((y ◇ (z ◇ w)) ◇ u) ◇ y) ◇ w) x).symm).trans (apc3 x ((((y ◇ (z ◇ w)) ◇ u) ◇ y) ◇ w) ((((y ◇ (z ◇ w)) ◇ u) ◇ y) ◇ w))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_24378_to_40624 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_24378_to_40624
