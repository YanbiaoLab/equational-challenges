-- Equation4754 → Equation55215
-- Recorded verdict: true
-- Premise: x = x ◇ (y ◇ (x ◇ (x ◇ (z ◇ y))))
-- Conclusion: x ◇ (y ◇ z) = x ◇ ((y ◇ z) ◇ y)
-- Original submission SHA-256: ae0db23f920f1a92031bbadd076903cd788bf5f94b9094e35a93d43177f9e679
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = x ◇ (y ◇ (x ◇ (x ◇ (z ◇ y))))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ z) = x ◇ ((y ◇ z) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have p0 : forall (q0 q1:G), (q1 ◇ ((q1 ◇ (q0 ◇ q1)) ◇ q1)) = q1:=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => (q1 ◇ (q0 ◇ q1)) ◇ t) ((h q1 q1 q0).symm))).symm).trans ((h q1 (q1 ◇ (q0 ◇ q1)) q1).symm)
  have p1 : forall (q0:G), (q0 ◇ (q0 ◇ q0)) = q0:=by
    intro q0
    exact ((cg (fun t => q0 ◇ t) (cg (fun t => t ◇ q0) (p0 q0 q0))).symm).trans (p0 (q0 ◇ (q0 ◇ q0)) q0)
  have p2 : forall (q0:G), (q0 ◇ q0) = q0:=by
    intro q0
    exact ((cg (fun t => q0 ◇ t) (p1 q0)).symm).trans (((cg (fun t => q0 ◇ t) (cg (fun t => q0 ◇ t) (cg (fun t => q0 ◇ t) (p1 q0)))).symm).trans ((h q0 q0 q0).symm))
  have p3 : forall (q0 q1:G), ((q1 ◇ q0) ◇ (q0 ◇ (q1 ◇ q0))) = (q1 ◇ q0):=by
    intro q0 q1
    exact ((cg (fun t => (q1 ◇ q0) ◇ t) (cg (fun t => q0 ◇ t) (p1 (q1 ◇ q0)))).symm).trans ((h (q1 ◇ q0) q0 q1).symm)
  have p4 : forall (q0 q1:G), (q0 ◇ (q1 ◇ (q0 ◇ (q0 ◇ q1)))) = q0:=by
    intro q0 q1
    exact ((cg (fun t => q0 ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => q0 ◇ t) (cg (fun t => q0 ◇ t) (p2 q1))))).symm).trans ((h q0 q1 q1).symm)
  have p5 : forall (q0 q1:G), ((q1 ◇ (q0 ◇ q1)) ◇ (q0 ◇ q1)) = (q1 ◇ (q0 ◇ q1)):=by
    intro q0 q1
    exact ((cg (fun t => (q1 ◇ (q0 ◇ q1)) ◇ t) (p3 q1 q0)).symm).trans (p3 (q0 ◇ q1) q1)
  have p6 : forall (q0 q1:G), ((q0 ◇ (q1 ◇ q0)) ◇ (q0 ◇ (q0 ◇ (q1 ◇ q0)))) = (q0 ◇ (q1 ◇ q0)):=by
    intro q0 q1
    exact ((cg (fun t => (q0 ◇ (q1 ◇ q0)) ◇ t) (cg (fun t => q0 ◇ t) (p2 (q0 ◇ (q1 ◇ q0))))).symm).trans (((cg (fun t => (q0 ◇ (q1 ◇ q0)) ◇ t) (cg (fun t => q0 ◇ t) (cg (fun t => (q0 ◇ (q1 ◇ q0)) ◇ t) (p5 q1 q0)))).symm).trans ((h (q0 ◇ (q1 ◇ q0)) q0 q1).symm))
  have p7 : forall (q0 q1 q2:G), (q2 ◇ ((q0 ◇ (q1 ◇ q0)) ◇ (q2 ◇ (q2 ◇ (q1 ◇ q0))))) = q2:=by
    intro q0 q1 q2
    exact ((cg (fun t => q2 ◇ t) (cg (fun t => (q0 ◇ (q1 ◇ q0)) ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => q2 ◇ t) (p3 q0 q1))))).symm).trans ((h q2 (q0 ◇ (q1 ◇ q0)) (q1 ◇ q0)).symm)
  have p8 : forall (q0 q1:G), (q1 ◇ (q1 ◇ (q0 ◇ q1))) = q1:=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (p6 q1 q0)).symm).trans (p7 q1 q0 q1)
  have p9 : forall (q0 q1:G), (q1 ◇ ((q0 ◇ q1) ◇ q1)) = q1:=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => (q0 ◇ q1) ◇ t) (p2 q1))).symm).trans (((cg (fun t => q1 ◇ t) (cg (fun t => (q0 ◇ q1) ◇ t) (cg (fun t => q1 ◇ t) (p8 q0 q1)))).symm).trans ((h q1 (q0 ◇ q1) q1).symm))
  have pa : forall (q0 q1:G), ((q0 ◇ (q1 ◇ (q1 ◇ q0))) ◇ q1) = (q0 ◇ (q1 ◇ (q1 ◇ q0))):=by
    intro q0 q1
    exact ((cg (fun t => (q0 ◇ (q1 ◇ (q1 ◇ q0))) ◇ t) (p4 q1 q0)).symm).trans (((cg (fun t => (q0 ◇ (q1 ◇ (q1 ◇ q0))) ◇ t) (cg (fun t => t ◇ (q0 ◇ (q1 ◇ (q1 ◇ q0)))) (p4 q1 q0))).symm).trans (p9 q1 (q0 ◇ (q1 ◇ (q1 ◇ q0)))))
  have pb : forall (q0 q1 q2:G), (q1 ◇ ((q2 ◇ (q0 ◇ q2)) ◇ (q1 ◇ (q1 ◇ q2)))) = q1:=by
    intro q0 q1 q2
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => (q2 ◇ (q0 ◇ q2)) ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => q1 ◇ t) (p8 q0 q2))))).symm).trans ((h q1 (q2 ◇ (q0 ◇ q2)) q2).symm)
  have pc : forall (q0 q1 q2:G), (q1 ◇ (((q0 ◇ q2) ◇ q2) ◇ (q1 ◇ (q1 ◇ q2)))) = q1:=by
    intro q0 q1 q2
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => ((q0 ◇ q2) ◇ q2) ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => q1 ◇ t) (p9 q0 q2))))).symm).trans ((h q1 ((q0 ◇ q2) ◇ q2) q2).symm)
  have pd : forall (q0 q1 q2:G), (q2 ◇ (((q0 ◇ q2) ◇ (q1 ◇ (q0 ◇ q2))) ◇ q2)) = q2:=by
    intro q0 q1 q2
    exact ((cg (fun t => q2 ◇ t) (cg (fun t => ((q0 ◇ q2) ◇ (q1 ◇ (q0 ◇ q2))) ◇ t) (p8 q0 q2))).symm).trans (pb q1 q2 (q0 ◇ q2))
  have pe : forall (q0 q1 q2:G), (q2 ◇ ((q0 ◇ q1) ◇ (q2 ◇ (q2 ◇ (q1 ◇ (q0 ◇ q1)))))) = q2:=by
    intro q0 q1 q2
    exact ((cg (fun t => q2 ◇ t) (cg (fun t => (q0 ◇ q1) ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => q2 ◇ t) (p5 q0 q1))))).symm).trans ((h q2 (q0 ◇ q1) (q1 ◇ (q0 ◇ q1))).symm)
  have pf : forall (q0 q1 q2:G), (q1 ◇ (q2 ◇ (q1 ◇ (q1 ◇ (q0 ◇ (q2 ◇ (q2 ◇ q0))))))) = q1:=by
    intro q0 q1 q2
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => q1 ◇ t) (pa q0 q2))))).symm).trans ((h q1 q2 (q0 ◇ (q2 ◇ (q2 ◇ q0)))).symm)
  have pg : forall (q0 q1 q2:G), (q2 ◇ (((q1 ◇ (q2 ◇ (q0 ◇ q2))) ◇ (q2 ◇ (q0 ◇ q2))) ◇ q2)) = q2:=by
    intro q0 q1 q2
    exact ((cg (fun t => q2 ◇ t) (cg (fun t => ((q1 ◇ (q2 ◇ (q0 ◇ q2))) ◇ (q2 ◇ (q0 ◇ q2))) ◇ t) (p2 q2))).symm).trans (((cg (fun t => q2 ◇ t) (cg (fun t => ((q1 ◇ (q2 ◇ (q0 ◇ q2))) ◇ (q2 ◇ (q0 ◇ q2))) ◇ t) (cg (fun t => q2 ◇ t) (p8 q0 q2)))).symm).trans (pc q1 q2 (q2 ◇ (q0 ◇ q2))))
  have ph : forall (q0 q1:G), (((q0 ◇ q1) ◇ q1) ◇ ((q0 ◇ q1) ◇ ((q0 ◇ q1) ◇ q1))) = ((q0 ◇ q1) ◇ q1):=by
    intro q0 q1
    exact ((cg (fun t => ((q0 ◇ q1) ◇ q1) ◇ t) (cg (fun t => t ◇ ((q0 ◇ q1) ◇ q1)) (pc q0 (q0 ◇ q1) q1))).symm).trans (((cg (fun t => ((q0 ◇ q1) ◇ q1) ◇ t) (cg (fun t => t ◇ ((q0 ◇ q1) ◇ q1)) (cg (fun t => t ◇ (((q0 ◇ q1) ◇ q1) ◇ ((q0 ◇ q1) ◇ ((q0 ◇ q1) ◇ q1)))) (pc q0 (q0 ◇ q1) q1)))).symm).trans (pg (q0 ◇ q1) (q0 ◇ q1) ((q0 ◇ q1) ◇ q1)))
  have pi : forall (q0 q1:G), ((q0 ◇ q1) ◇ ((q0 ◇ q1) ◇ q1)) = (q0 ◇ q1):=by
    intro q0 q1
    exact ((cg (fun t => (q0 ◇ q1) ◇ t) (ph q0 q1)).symm).trans (pc q0 (q0 ◇ q1) q1)
  have pj : forall (q0 q1 q2:G), ((q0 ◇ (q2 ◇ q1)) ◇ (q1 ◇ (q0 ◇ (q2 ◇ q1)))) = (q0 ◇ (q2 ◇ q1)):=by
    intro q0 q1 q2
    exact ((cg (fun t => (q0 ◇ (q2 ◇ q1)) ◇ t) (cg (fun t => q1 ◇ t) (pi q0 (q2 ◇ q1)))).symm).trans ((h (q0 ◇ (q2 ◇ q1)) q1 q2).symm)
  have pk : forall (q0 q1 q2:G), ((q1 ◇ (q0 ◇ (q2 ◇ q1))) ◇ (q0 ◇ (q2 ◇ q1))) = (q1 ◇ (q0 ◇ (q2 ◇ q1))):=by
    intro q0 q1 q2
    exact ((cg (fun t => (q1 ◇ (q0 ◇ (q2 ◇ q1))) ◇ t) (pj q0 q1 q2)).symm).trans (((cg (fun t => (q1 ◇ (q0 ◇ (q2 ◇ q1))) ◇ t) (cg (fun t => t ◇ (q1 ◇ (q0 ◇ (q2 ◇ q1)))) (pj q0 q1 q2))).symm).trans (p9 (q0 ◇ (q2 ◇ q1)) (q1 ◇ (q0 ◇ (q2 ◇ q1)))))
  have pl : forall (q0 q1 q2 q3:G), (q2 ◇ ((((q0 ◇ q3) ◇ (q1 ◇ (q0 ◇ q3))) ◇ q3) ◇ (q2 ◇ (q2 ◇ q3)))) = q2:=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => q2 ◇ t) (cg (fun t => (((q0 ◇ q3) ◇ (q1 ◇ (q0 ◇ q3))) ◇ q3) ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => q2 ◇ t) (pd q0 q1 q3))))).symm).trans ((h q2 (((q0 ◇ q3) ◇ (q1 ◇ (q0 ◇ q3))) ◇ q3) q3).symm)
  have pm : forall (q0 q1 q2:G), (q2 ◇ ((q0 ◇ (q1 ◇ (q1 ◇ q0))) ◇ (q2 ◇ (q2 ◇ (q1 ◇ (q1 ◇ q0)))))) = q2:=by
    intro q0 q1 q2
    exact (((cg (fun t => q2 ◇ t) (cg (fun t => t ◇ (q2 ◇ (q2 ◇ (q1 ◇ (q1 ◇ q0))))) (cg (fun t => t ◇ (q1 ◇ (q1 ◇ q0))) (pa q0 q1)))).trans (cg (fun t => q2 ◇ t) (cg (fun t => t ◇ (q2 ◇ (q2 ◇ (q1 ◇ (q1 ◇ q0))))) (pk q1 q0 q1)))).symm).trans (((cg (fun t => q2 ◇ t) (cg (fun t => t ◇ (q2 ◇ (q2 ◇ (q1 ◇ (q1 ◇ q0))))) (cg (fun t => t ◇ (q1 ◇ (q1 ◇ q0))) (cg (fun t => (q0 ◇ (q1 ◇ (q1 ◇ q0))) ◇ t) (p4 q1 q0))))).symm).trans (pl q0 q1 q2 (q1 ◇ (q1 ◇ q0))))
  have pn : forall (q0 q1:G), ((q0 ◇ (q1 ◇ (q1 ◇ q0))) ◇ (q0 ◇ (q0 ◇ (q1 ◇ (q1 ◇ q0))))) = (q0 ◇ (q1 ◇ (q1 ◇ q0))):=by
    intro q0 q1
    exact ((cg (fun t => (q0 ◇ (q1 ◇ (q1 ◇ q0))) ◇ t) (cg (fun t => t ◇ (q0 ◇ (q1 ◇ (q1 ◇ q0)))) (pm q0 q1 q0))).symm).trans (((cg (fun t => (q0 ◇ (q1 ◇ (q1 ◇ q0))) ◇ t) (cg (fun t => t ◇ (q0 ◇ (q1 ◇ (q1 ◇ q0)))) (cg (fun t => t ◇ ((q0 ◇ (q1 ◇ (q1 ◇ q0))) ◇ (q0 ◇ (q0 ◇ (q1 ◇ (q1 ◇ q0)))))) (pm q0 q1 q0)))).symm).trans (pg q0 q0 (q0 ◇ (q1 ◇ (q1 ◇ q0)))))
  have po : forall (q0 q1:G), (q1 ◇ (q1 ◇ (q0 ◇ (q0 ◇ q1)))) = q1:=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (pn q1 q0)).symm).trans (pm q1 q0 q1)
  have pp : forall (q0 q1:G), (q0 ◇ (q1 ◇ q0)) = q0:=by
    intro q0 q1
    exact ((cg (fun t => q0 ◇ t) (cg (fun t => q1 ◇ t) (p2 q0))).symm).trans (((cg (fun t => q0 ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => q0 ◇ t) (po q1 q0)))).symm).trans (pf q0 q0 q1))
  have pq : forall (q0 q1:G), ((q0 ◇ (q1 ◇ (q1 ◇ q0))) ◇ q0) = (q0 ◇ (q1 ◇ (q1 ◇ q0))):=by
    intro q0 q1
    exact ((cg (fun t => (q0 ◇ (q1 ◇ (q1 ◇ q0))) ◇ t) (po q1 q0)).symm).trans (pn q0 q1)
  have pr : forall (q0 q1 q2:G), (q2 ◇ ((q0 ◇ q1) ◇ (q2 ◇ (q2 ◇ q1)))) = q2:=by
    intro q0 q1 q2
    exact ((cg (fun t => q2 ◇ t) (cg (fun t => (q0 ◇ q1) ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => q2 ◇ t) (pp q1 q0))))).symm).trans (pe q0 q1 q2)
  have ps : forall (q0 q1:G), (q1 ◇ (q1 ◇ q0)) = q1:=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (pp (q1 ◇ q0) q1)).symm).trans (pr q1 q0 q1)
  have pt : forall (q0 q1:G), ((q0 ◇ q1) ◇ q0) = (q0 ◇ q1):=by
    intro q0 q1
    exact ((cg (fun t => t ◇ q0) (cg (fun t => q0 ◇ t) (ps q0 q1))).symm).trans ((pq q0 q1).trans (cg (fun t => q0 ◇ t) (ps q0 q1)))
  exact (calc
    (x ◇ (y ◇ z)) = (x ◇ (y ◇ z)):=rfl
    _ = (x ◇ ((y ◇ z) ◇ y)):=(cg (fun t => x ◇ t) (pt y z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_4754_to_55215 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_4754_to_55215
