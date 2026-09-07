-- Equation42547 → Equation41730
-- Recorded verdict: true
-- Premise: x ◇ x = y ◇ (z ◇ ((x ◇ w) ◇ w))
-- Conclusion: x ◇ x = y ◇ (z ◇ (w ◇ (u ◇ u)))
-- Original submission SHA-256: 881cebe49ae55f7d5338085a1c39dbe4ea646eae021bfd0b8ab7422bbce4301c
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = y ◇ (z ◇ ((x ◇ w) ◇ w))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ x = y ◇ (z ◇ (w ◇ (u ◇ u)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have p0 : forall (q0 q1 q2:G), (q2 ◇ (q0 ◇ q0)) = (q1 ◇ q1):=by
    intro q0 q1 q2
    exact ((cg (fun t => q2 ◇ t) ((h q0 q0 (q1 ◇ ((q0 ◇ q0) ◇ q0)) q0).symm)).symm).trans ((h q1 q2 q0 ((q0 ◇ q0) ◇ q0)).symm)
  have p1 : forall (q0 q1 q2:G), (q1 ◇ q1) = (q0 ◇ q0):=by
    intro q0 q1 q2
    exact ((p0 q0 q1 q2).symm).trans (p0 q0 q0 q2)
  have p2 : forall (q0 q1 q2:G), (q2 ◇ (q0 ◇ q0)) = (q1 ◇ (q1 ◇ q1)):=by
    intro q0 q1 q2
    exact (p0 q0 q1 q2).trans ((p0 q1 q1 q1).symm)
  have p3 : forall (q0 q1 q2 q3:G), (q2 ◇ (q3 ◇ ((q0 ◇ q0) ◇ q1))) = (q1 ◇ q1):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => q2 ◇ t) (cg (fun t => q3 ◇ t) (cg (fun t => t ◇ q1) (p1 q0 q1 q0)))).symm).trans ((h q1 q2 q3 q1).symm)
  have p4 : forall (q1 q3 q4 q0 q2:G), (q3 ◇ (q4 ◇ (q1 ◇ q1))) = (q1 ◇ q1):=by
    intro q1 q3 q4 q0 q2
    exact (((cg (fun t => q3 ◇ t) (cg (fun t => q4 ◇ t) (p3 q0 q1 (q0 ◇ q0) q2))).symm).trans (p3 q0 (q2 ◇ ((q0 ◇ q0) ◇ q1)) q3 q4)).trans (p3 q0 q1 (q2 ◇ ((q0 ◇ q0) ◇ q1)) q2)
  have p5 : forall (q0 q1:G), ((q0 ◇ q0) ◇ (q0 ◇ q0)) = (q1 ◇ (q0 ◇ q0)):=by
    intro q0 q1
    exact (((cg (fun t => q1 ◇ t) (p4 q0 q0 (q0 ◇ q0) q0 q0)).symm).trans (p4 (q0 ◇ q0) q1 q0 q0 q0)).symm
  have p6 : forall (q0 q1:G), (q1 ◇ (q0 ◇ q0)) = (q0 ◇ (q0 ◇ q0)):=by
    intro q0 q1
    exact ((p5 q0 q1).symm).trans (p5 q0 q0)
  have p7 : forall (q0 q1 q2 q3 q4:G), (q3 ◇ (q1 ◇ (q1 ◇ q1))) = (q1 ◇ (q1 ◇ (q1 ◇ q1))):=by
    intro q0 q1 q2 q3 q4
    exact ((cg (fun t => q3 ◇ t) (p6 q1 q4)).symm).trans ((p4 q1 q3 q4 q0 q2).trans ((p4 q1 q1 q1 q0 q2).symm))
  have p8 : forall (q0 q1 q2 q3 q4:G), (q1 ◇ (q1 ◇ (q1 ◇ q1))) = (q1 ◇ q1):=by
    intro q0 q1 q2 q3 q4
    exact ((p7 (q3 ◇ (q1 ◇ (q1 ◇ q1))) q1 (q3 ◇ (q1 ◇ (q1 ◇ q1))) q3 (q3 ◇ (q1 ◇ (q1 ◇ q1)))).symm).trans (((cg (fun t => q3 ◇ t) (p6 q1 q4)).symm).trans (p4 q1 q3 q4 q0 q2))
  have p9 : forall (q0 q1 q2 q3:G), ((q0 ◇ q0) ◇ (q1 ◇ (q1 ◇ q1))) = (q2 ◇ (q2 ◇ q2)):=by
    intro q0 q1 q2 q3
    exact (((cg (fun t => (q0 ◇ q0) ◇ t) (p2 q0 q1 (q0 ◇ q0))).symm).trans ((p2 q2 (q0 ◇ q0) q3).symm)).trans (p6 q2 q3)
  have pa : forall (q2 q3 q4 q0 q1:G), (q3 ◇ (q4 ◇ (q2 ◇ (q2 ◇ q2)))) = (q2 ◇ q2):=by
    intro q2 q3 q4 q0 q1
    exact ((cg (fun t => q3 ◇ t) (cg (fun t => q4 ◇ t) (p6 q2 ((q0 ◇ q0) ◇ (q1 ◇ (q1 ◇ q1)))))).symm).trans (((cg (fun t => q3 ◇ t) (cg (fun t => q4 ◇ t) (cg (fun t => t ◇ (q2 ◇ q2)) ((p9 q0 q1 q2 q0).symm)))).symm).trans ((h q2 q3 q4 (q2 ◇ q2)).symm))
  have pb : forall (q0 q1:G), (q0 ◇ (q0 ◇ q0)) = (q0 ◇ q0):=by
    intro q0 q1
    exact ((p6 q0 q1).symm).trans (((cg (fun t => q1 ◇ t) (p8 q0 q0 q0 q0 q0)).symm).trans (pa q0 q1 q0 q0 q0))
  have pc : forall (q0 q1:G), (q1 ◇ (q0 ◇ q0)) = (q0 ◇ q0):=by
    intro q0 q1
    exact (p6 q0 q1).trans (pb q0 (q0 ◇ (q0 ◇ q0)))
  exact (calc
    (x ◇ x) = (y ◇ (x ◇ x)):=(pc x y).symm
    _ = (y ◇ (z ◇ (x ◇ x))):=cg (fun t => y ◇ t) ((pc x z).symm)
    _ = (y ◇ (z ◇ (u ◇ u))):=(cg (fun t => y ◇ t) (cg (fun t => z ◇ t) (p1 x u u))).symm
    _ = (y ◇ (z ◇ (w ◇ (u ◇ u)))):=(cg (fun t => y ◇ t) (cg (fun t => z ◇ t) (pc u w))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_42547_to_41730 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_42547_to_41730
