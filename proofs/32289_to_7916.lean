-- Equation32289 → Equation7916
-- Recorded verdict: true
-- Premise: x = (y * ((y * (y * y)) * z)) * x
-- Conclusion: x = y * (z * ((y * (x * z)) * x))
-- Original submission SHA-256: 4a7172aac72ce984cf29bba34556bb6bc187e9e34ba2b3b69539638e02c4a215
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ ((y ◇ (y ◇ y)) ◇ z)) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (z ◇ ((y ◇ (x ◇ z)) ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z:G), ((y ◇ ((y ◇ (y ◇ y)) ◇ z)) ◇ x) = ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have apc2 : forall (q0:G), ((q0 ◇ ((q0 ◇ (q0 ◇ q0)) ◇ q0)) ◇ q0) = q0:=by
    intro q0
    exact ((apc0 q0 q0 q0).symm).trans ((h q0 q0 q0).symm)
  have apc3 : forall (q1 q2 q3 q4:G), (((q1 ◇ ((q1 ◇ (q1 ◇ q1)) ◇ q2)) ◇ (((q1 ◇ ((q1 ◇ (q1 ◇ q1)) ◇ q2)) ◇ (q1 ◇ ((q1 ◇ (q1 ◇ q1)) ◇ q2))) ◇ q4)) ◇ q3) = q3:=by
    intro q1 q2 q3 q4
    exact ((congrArg (fun t => t ◇ q3) (congrArg (fun t => (q1 ◇ ((q1 ◇ (q1 ◇ q1)) ◇ q2)) ◇ t) (congrArg (fun t => t ◇ q4) ((h ((q1 ◇ ((q1 ◇ (q1 ◇ q1)) ◇ q2)) ◇ (q1 ◇ ((q1 ◇ (q1 ◇ q1)) ◇ q2))) q1 q2).symm)))).symm).trans ((h q3 (q1 ◇ ((q1 ◇ (q1 ◇ q1)) ◇ q2)) q4).symm)
  have apc4 : forall (q5 q6 q7 q8:G), (((q5 ◇ ((q5 ◇ (q5 ◇ q5)) ◇ q6)) ◇ ((q5 ◇ ((q5 ◇ (q5 ◇ q5)) ◇ q6)) ◇ q8)) ◇ q7) = q7:=by
    intro q5 q6 q7 q8
    exact ((congrArg (fun t => t ◇ q7) (congrArg (fun t => (q5 ◇ ((q5 ◇ (q5 ◇ q5)) ◇ q6)) ◇ t) (congrArg (fun t => t ◇ q8) ((h (q5 ◇ ((q5 ◇ (q5 ◇ q5)) ◇ q6)) q5 q6).symm)))).symm).trans (apc3 q5 q6 q7 q8)
  have apc5 : forall (q9 q10 q11 q12:G), (q10 ◇ q9) = q9:=by
    intro q9 q10 q11 q12
    exact ((congrArg (fun t => t ◇ q9) (apc4 q11 q12 q10 (q11 ◇ ((q11 ◇ (q11 ◇ q11)) ◇ q12)))).symm).trans ((((congrArg (fun t => t ◇ q9) ((h (((q11 ◇ ((q11 ◇ (q11 ◇ q11)) ◇ q12)) ◇ ((q11 ◇ ((q11 ◇ (q11 ◇ q11)) ◇ q12)) ◇ (q11 ◇ ((q11 ◇ (q11 ◇ q11)) ◇ q12)))) ◇ q10) q11 q12).symm)).symm).trans (apc0 q9 (q11 ◇ ((q11 ◇ (q11 ◇ q11)) ◇ q12)) q10)).trans (apc2 q9))
  exact (calc
    x = x:=rfl
    _ = (y ◇ (z ◇ ((y ◇ (x ◇ z)) ◇ x))):=(((((congrArg (fun t => y ◇ t) (congrArg (fun t => z ◇ t) (congrArg (fun t => t ◇ x) (congrArg (fun t => y ◇ t) (apc5 z x (x ◇ z) (x ◇ z)))))).trans (congrArg (fun t => y ◇ t) (congrArg (fun t => z ◇ t) (congrArg (fun t => t ◇ x) (apc5 z y (y ◇ z) (y ◇ z)))))).trans (congrArg (fun t => y ◇ t) (congrArg (fun t => z ◇ t) (apc5 x z (z ◇ x) (z ◇ x))))).trans (congrArg (fun t => y ◇ t) (apc5 x z (z ◇ x) (z ◇ x)))).trans (apc5 x y (y ◇ x) (y ◇ x))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_32289_to_7916 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_32289_to_7916
