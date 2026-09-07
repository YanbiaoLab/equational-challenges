-- Equation44661 → Equation44329
-- Recorded verdict: true
-- Premise: x * y = y * ((z * (w * u)) * z)
-- Conclusion: x * x = y * ((z * (z * z)) * y)
-- Original submission SHA-256: 5da683c0e4317d9512524ea4b4c6cd30482c863de85780db08956880c97337e8
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = y ◇ ((z ◇ (w ◇ u)) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ ((z ◇ (z ◇ z)) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc1 : forall (x y z w u:G), (y ◇ y) = (x ◇ y):=by
    intro x y z w u
    exact ((h x y z w u).trans ((h y y z w u).symm)).symm
  have apc2 : forall (q0 q1 q2 q3:G), (q2 ◇ ((q3 ◇ (q1 ◇ q0)) ◇ q3)) = (q2 ◇ q2):=by
    intro q0 q1 q2 q3
    exact ((apc1 q0 q2 q0 q0 q0).trans (h q0 q2 q3 q1 q0)).symm
  have apc4 : forall (q4 q5 q6 q7 q8 q9 q10:G), (q6 ◇ (((q5 ◇ q4) ◇ (q5 ◇ q4)) ◇ q7)) = (q6 ◇ q6):=by
    intro q4 q5 q6 q7 q8 q9 q10
    exact ((congrArg (fun t => q6 ◇ t) (congrArg (fun t => t ◇ q7) (apc2 q8 q9 (q5 ◇ q4) q10))).symm).trans (((congrArg (fun t => q6 ◇ t) (congrArg (fun t => t ◇ q7) (h q7 (q5 ◇ q4) q10 q9 q8))).symm).trans (apc2 q4 q5 q6 q7))
  have apc5 : forall (q11 q12 q13 q14 q15:G), (q14 ◇ ((q11 ◇ (q13 ◇ q12)) ◇ q15)) = (q14 ◇ q14):=by
    intro q11 q12 q13 q14 q15
    exact ((congrArg (fun t => q14 ◇ t) (congrArg (fun t => t ◇ q15) (apc1 q11 (q13 ◇ q12) q11 q11 q11))).symm).trans (apc4 q12 q13 q14 q15 q11 q11 q11)
  have apc7 : forall (q16 q17 q18 q19:G), (q18 ◇ ((q16 ◇ q17) ◇ q19)) = (q18 ◇ q18):=by
    intro q16 q17 q18 q19
    exact ((congrArg (fun t => q18 ◇ t) (congrArg (fun t => t ◇ q19) ((h q16 q17 q16 q16 q16).symm))).symm).trans (apc5 q17 q16 (q16 ◇ (q16 ◇ q16)) q18 q19)
  have apc8 : forall (q6 q7 q10 q9 q8:G), (q6 ◇ (q7 ◇ q7)) = (q6 ◇ q6):=by
    intro q6 q7 q10 q9 q8
    exact ((congrArg (fun t => q6 ◇ t) (apc7 q10 (q9 ◇ q8) q7 q10)).symm).trans (((congrArg (fun t => q6 ◇ t) (h (q7 ◇ (q8 ◇ q8)) q7 q10 q9 q8)).symm).trans (apc2 q8 q8 q6 q7))
  have apc9 : forall (q20 q21 q22:G), (q21 ◇ (q20 ◇ q22)) = (q21 ◇ q21):=by
    intro q20 q21 q22
    exact ((congrArg (fun t => q21 ◇ t) (apc1 q20 q22 q20 q20 q20)).symm).trans (apc8 q21 q22 q20 q20 q20)
  have apc10 : forall (q23 q24 q25:G), (q24 ◇ q25) = (q23 ◇ q25):=by
    intro q23 q24 q25
    exact ((h q23 q25 q23 q23 q23).trans ((h q24 q25 q23 q23 q23).symm)).symm
  have apc11 : forall (q26 q27 q28 q29 q30 q31:G), (q27 ◇ q28) = (q26 ◇ q26):=by
    intro q26 q27 q28 q29 q30 q31
    exact ((((congrArg (fun t => q26 ◇ t) (congrArg (fun t => t ◇ q29) (apc9 q30 q29 q31))).trans (apc9 (q29 ◇ q29) q26 q29)).symm).trans (((apc10 q26 q28 ((q29 ◇ (q30 ◇ q31)) ◇ q29)).symm).trans ((h q27 q28 q29 q30 q31).symm))).symm
  exact (apc11 (x ◇ x) x x (x ◇ x) (x ◇ x) (x ◇ x)).trans ((apc11 (x ◇ x) y ((z ◇ (z ◇ z)) ◇ y) (x ◇ x) (x ◇ x) (x ◇ x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_44661_to_44329 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_44661_to_44329
