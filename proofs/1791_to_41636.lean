-- Equation1791 → Equation41636
-- Recorded verdict: true
-- Premise: x = (y ◇ z) ◇ ((z ◇ x) ◇ z)
-- Conclusion: x ◇ x = y ◇ (y ◇ (y ◇ (z ◇ z)))
-- Original submission SHA-256: 7172a03a90e051ba65d62c444ef78bb6d0317c8cf72b355b4495e5f2307443ae
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ z) ◇ ((z ◇ x) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ (y ◇ (y ◇ (z ◇ z)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3:G), ((q3 ◇ (q1 ◇ q2)) ◇ (q0 ◇ (q1 ◇ q2))) = ((q2 ◇ q0) ◇ q2):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => (q3 ◇ (q1 ◇ q2)) ◇ t) (congrArg (fun t => t ◇ (q1 ◇ q2)) ((h q0 q1 q2).symm))).symm).trans ((h ((q2 ◇ q0) ◇ q2) q3 (q1 ◇ q2)).symm)
  have apc1 : forall (q4 q5 q6:G), (q4 ◇ (q5 ◇ ((q6 ◇ q4) ◇ q6))) = ((q6 ◇ q5) ◇ q6):=by
    intro q4 q5 q6
    exact ((congrArg (fun t => t ◇ (q5 ◇ ((q6 ◇ q4) ◇ q6))) ((h q4 q4 q6).symm)).symm).trans (apc0 q5 (q6 ◇ q4) q6 (q4 ◇ q6))
  have apc2 : forall (q7 q8 q9:G), ((q9 ◇ (q7 ◇ q9)) ◇ q9) = (q8 ◇ q8):=by
    intro q7 q8 q9
    exact (((congrArg (fun t => q8 ◇ t) ((h q8 q7 q9).symm)).symm).trans (apc1 q8 (q7 ◇ q9) q9)).symm
  have apc3 : forall (q7 q8 q9:G), (q8 ◇ q8) = (q7 ◇ q7):=by
    intro q7 q8 q9
    exact ((apc2 q7 q8 q9).symm).trans (apc2 q7 q7 q9)
  have apc4 : forall (q10 q11:G), (q10 ◇ q10) = q11:=by
    intro q10 q11
    exact ((apc3 q10 ((q10 ◇ q11) ◇ q10) q10).symm).trans ((h q11 (q10 ◇ q11) q10).symm)
  exact (apc4 x (x ◇ x)).trans (apc4 x (y ◇ (y ◇ (y ◇ (z ◇ z)))))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_1791_to_41636 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_1791_to_41636
