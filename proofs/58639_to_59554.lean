-- Equation58639 → Equation59554
-- Recorded verdict: true
-- Premise: (x ◇ y) ◇ y = z ◇ (y ◇ (x ◇ z))
-- Conclusion: (x ◇ y) ◇ y = z ◇ ((w ◇ y) ◇ y)
-- Original submission SHA-256: 4b732097c3ea847f8dc207621f8cde3efd5a0923832b94643fc783308fb05067
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ y = z ◇ (y ◇ (x ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ y = z ◇ ((w ◇ y) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z:G), (z ◇ (y ◇ (x ◇ z))) = (x ◇ (y ◇ (x ◇ x))):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have apc1 : forall (x y z:G), ((x ◇ y) ◇ y) = (x ◇ (y ◇ (x ◇ x))):=by
    intro x y z
    exact (h x y x).trans (apc0 x y x)
  have apc2 : forall (q0 q1 q2:G), ((q0 ◇ q2) ◇ ((q0 ◇ q1) ◇ q1)) = ((q1 ◇ q2) ◇ q2):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => (q0 ◇ q2) ◇ t) ((h q0 q1 q2).symm)).symm).trans ((h q1 q2 (q0 ◇ q2)).symm)
  have apc6 : forall (q3 q4 q5:G), (((q3 ◇ q5) ◇ (q3 ◇ q4)) ◇ (q3 ◇ q4)) = (q5 ◇ ((q5 ◇ q4) ◇ q4)):=by
    intro q3 q4 q5
    exact (((congrArg (fun t => q5 ◇ t) (apc2 q3 q5 q4)).symm).trans ((h (q3 ◇ q5) (q3 ◇ q4) q5).symm)).symm
  have apc8 : forall (q0 q6 q1 q2:G), ((q6 ◇ (q0 ◇ q1)) ◇ (q2 ◇ ((q0 ◇ q6) ◇ q6))) = ((q1 ◇ q2) ◇ q2):=by
    intro q0 q6 q1 q2
    exact ((congrArg (fun t => (q6 ◇ (q0 ◇ q1)) ◇ t) (congrArg (fun t => q2 ◇ t) ((h q0 q6 q1).symm))).symm).trans ((h q1 q2 (q6 ◇ (q0 ◇ q1))).symm)
  have apc9 : forall (q7 q8 q9:G), ((q9 ◇ (q8 ◇ q7)) ◇ (q8 ◇ q7)) = ((q7 ◇ (q8 ◇ q9)) ◇ (q8 ◇ q9)):=by
    intro q7 q8 q9
    exact (((apc2 q7 q7 (q8 ◇ q9)).symm).trans (((congrArg (fun t => (q7 ◇ (q8 ◇ q9)) ◇ t) (apc2 q8 q7 q7)).symm).trans (apc8 q8 q7 q9 (q8 ◇ q7)))).symm
  have apc10 : forall (q10 q11 q12:G), (q12 ◇ ((q11 ◇ q10) ◇ (q12 ◇ q12))) = ((q10 ◇ (q11 ◇ q12)) ◇ (q11 ◇ q12)):=by
    intro q10 q11 q12
    exact (((apc9 q10 q11 q12).symm).trans (apc1 q12 (q11 ◇ q10) q10)).symm
  have apc11 : forall (q13 q14:G), (q14 ◇ ((q14 ◇ q13) ◇ q13)) = ((q13 ◇ q14) ◇ q14):=by
    intro q13 q14
    exact (((apc2 (q14 ◇ q14) (q13 ◇ q14) (q13 ◇ q13)).trans (apc6 q13 q13 q14)).symm).trans (((congrArg (fun t => ((q14 ◇ q14) ◇ (q13 ◇ q13)) ◇ t) (apc10 (q14 ◇ q14) q13 q14)).symm).trans (apc8 q13 (q14 ◇ q14) q13 q14))
  have apc12 : forall (q15 q16:G), (((q15 ◇ q16) ◇ q15) ◇ q15) = ((q15 ◇ q16) ◇ q16):=by
    intro q15 q16
    exact (((apc11 q15 q16).symm).trans (((congrArg (fun t => q16 ◇ t) (apc11 q16 q15)).symm).trans ((h (q15 ◇ q16) q15 q16).symm))).symm
  have apc13 : forall (q17 q18:G), ((q17 ◇ (q17 ◇ q18)) ◇ (q17 ◇ q18)) = ((q18 ◇ q17) ◇ q17):=by
    intro q17 q18
    exact ((apc2 q17 q17 (q17 ◇ q18)).symm).trans (((congrArg (fun t => (q17 ◇ (q17 ◇ q18)) ◇ t) (apc11 q17 q17)).symm).trans (apc8 q17 q17 q18 q17))
  have apc14 : forall (q19 q20:G), (q20 ◇ ((q19 ◇ q20) ◇ q20)) = ((q20 ◇ q19) ◇ q19):=by
    intro q19 q20
    exact (((congrArg (fun t => q20 ◇ t) (apc13 q20 q19)).symm).trans (apc11 (q20 ◇ q19) q20)).trans (apc12 q20 q19)
  have apc15 : forall (q21 q22 q23:G), ((q23 ◇ q22) ◇ q22) = ((q23 ◇ q21) ◇ q21):=by
    intro q21 q22 q23
    exact ((((apc2 q22 q21 (q21 ◇ q23)).trans (apc13 q21 q23)).symm).trans (((congrArg (fun t => (q22 ◇ (q21 ◇ q23)) ◇ t) (apc14 q21 q22)).symm).trans (apc8 q21 q22 q23 q22))).symm
  have apc16 : forall (q24 q25 q26:G), ((q25 ◇ q26) ◇ q26) = ((q24 ◇ q26) ◇ q26):=by
    intro q24 q25 q26
    exact (((apc11 q24 q26).symm).trans (((congrArg (fun t => q26 ◇ t) (apc15 q24 q25 q26)).symm).trans (apc11 q25 q26))).symm
  have apc17 : forall (q27 q28 q29:G), ((q29 ◇ q28) ◇ q28) = ((q28 ◇ q27) ◇ q27):=by
    intro q27 q28 q29
    exact (((apc15 q27 (q28 ◇ q29) q28).symm).trans (apc13 q28 q29)).symm
  have apc18 : forall (q30 q31 q32 q33:G), ((q33 ◇ q31) ◇ q31) = ((q30 ◇ q32) ◇ q32):=by
    intro q30 q31 q32 q33
    exact (((apc16 q30 q33 q32).symm).trans (apc15 q31 q32 q33)).symm
  have apc20 : forall (q30 q31 q32 q33:G), ((q31 ◇ q31) ◇ q31) = ((q30 ◇ q32) ◇ q32):=by
    intro q30 q31 q32 q33
    exact (((apc18 q30 q31 q32 q30).symm).trans (apc18 q31 q31 q31 q30)).symm
  have apc27 : forall (q34 q35 q36:G), (q36 ◇ ((q35 ◇ q34) ◇ q34)) = ((q36 ◇ q35) ◇ q35):=by
    intro q34 q35 q36
    exact ((congrArg (fun t => q36 ◇ t) (apc15 q34 q36 q35)).symm).trans (apc14 q35 q36)
  have apc33 : forall (q37 q38:G), ((q38 ◇ q37) ◇ q37) = ((q37 ◇ q38) ◇ q38):=by
    intro q37 q38
    exact ((apc27 q37 q37 q38).symm).trans (((congrArg (fun t => q38 ◇ t) (apc17 q37 q37 q38)).symm).trans (apc11 q37 q38))
  have apc34 : forall (q39 q40 q41:G), (q41 ◇ ((q39 ◇ q40) ◇ q40)) = ((q40 ◇ q41) ◇ q41):=by
    intro q39 q40 q41
    exact (((congrArg (fun t => q41 ◇ t) ((apc17 q41 q40 q39).symm)).symm).trans (apc14 q40 q41)).trans (apc33 q40 q41)
  exact (calc
    ((x ◇ y) ◇ y) = ((w ◇ w) ◇ w):=(apc20 x w y w).symm
    _ = ((y ◇ z) ◇ z):=((apc20 y w z w).symm).symm
    _ = (z ◇ ((w ◇ y) ◇ y)):=(apc34 w y z).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_58639_to_59554 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_58639_to_59554
