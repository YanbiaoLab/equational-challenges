-- Equation19010 → Equation32498
-- Recorded verdict: true
-- Premise: x = (y ◇ x) ◇ ((z ◇ x) ◇ (y ◇ z))
-- Conclusion: x = (y ◇ ((z ◇ (y ◇ z)) ◇ x)) ◇ x
-- Original submission SHA-256: c46a050f17c704beef3934f5a623e7cf1e7dce57843c5069bc464633babad866
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ x) ◇ ((z ◇ x) ◇ (y ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ ((z ◇ (y ◇ z)) ◇ x)) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have p0 : forall (q0 q1 q2 q3:G), (((q1 ◇ q0) ◇ q3) ◇ ((((q2 ◇ q0) ◇ (q1 ◇ q2)) ◇ q3) ◇ q0)) = q3:=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => ((q1 ◇ q0) ◇ q3) ◇ t) (cg (fun t => (((q2 ◇ q0) ◇ (q1 ◇ q2)) ◇ q3) ◇ t) ((h q0 q1 q2).symm))).symm).trans ((h q3 (q1 ◇ q0) ((q2 ◇ q0) ◇ (q1 ◇ q2))).symm)
  have p1 : forall (q0 q1 q2 q3:G), ((q3 ◇ ((q2 ◇ q0) ◇ (q1 ◇ q2))) ◇ (q0 ◇ (q3 ◇ (q1 ◇ q0)))) = ((q2 ◇ q0) ◇ (q1 ◇ q2)):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => (q3 ◇ ((q2 ◇ q0) ◇ (q1 ◇ q2))) ◇ t) (cg (fun t => t ◇ (q3 ◇ (q1 ◇ q0))) ((h q0 q1 q2).symm))).symm).trans ((h ((q2 ◇ q0) ◇ (q1 ◇ q2)) q3 (q1 ◇ q0)).symm)
  have p2 : forall (q0 q1 q2:G), ((((q1 ◇ q0) ◇ q0) ◇ ((q2 ◇ (q1 ◇ q0)) ◇ (q1 ◇ q2))) ◇ q0) = ((q2 ◇ (q1 ◇ q0)) ◇ (q1 ◇ q2)):=by
    intro q0 q1 q2
    exact ((cg (fun t => (((q1 ◇ q0) ◇ q0) ◇ ((q2 ◇ (q1 ◇ q0)) ◇ (q1 ◇ q2))) ◇ t) ((h q0 q1 (q1 ◇ q0)).symm)).symm).trans (p1 (q1 ◇ q0) q1 q2 ((q1 ◇ q0) ◇ q0))
  have p3 : forall (q0 q1 q2:G), (q0 ◇ (q0 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0)))) = ((q2 ◇ q0) ◇ (q1 ◇ q2)):=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ (q0 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0)))) ((h q0 q1 q2).symm)).symm).trans (p1 q0 q1 q2 (q1 ◇ q0))
  have p4 : forall (q0 q1 q2:G), ((q2 ◇ q0) ◇ (q1 ◇ q2)) = ((q0 ◇ q0) ◇ (q1 ◇ q0)):=by
    intro q0 q1 q2
    exact ((p3 q0 q1 q2).symm).trans (p3 q0 q1 q0)
  have p5 : forall (q0 q1:G), ((q1 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) = q0:=by
    intro q0 q1
    exact ((cg (fun t => (q1 ◇ q0) ◇ t) (p4 q0 q1 q0)).symm).trans ((h q0 q1 q0).symm)
  have p6 : forall (q0 q1:G), (((q1 ◇ q1) ◇ ((q1 ◇ (q0 ◇ q1)) ◇ q1)) ◇ q1) = ((q1 ◇ (q0 ◇ q1)) ◇ (q0 ◇ q1)):=by
    intro q0 q1
    exact ((cg (fun t => t ◇ q1) (p4 q1 (q1 ◇ (q0 ◇ q1)) (q0 ◇ q1))).symm).trans (p2 q1 q0 q1)
  have p7 : forall (q0 q1 q3 q2:G), (q0 ◇ ((q3 ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) ◇ ((q1 ◇ q0) ◇ q3))) = ((q0 ◇ q0) ◇ (q1 ◇ q0)):=by
    intro q0 q1 q3 q2
    exact ((cg (fun t => q0 ◇ t) (cg (fun t => t ◇ ((q1 ◇ q0) ◇ q3)) (cg (fun t => q3 ◇ t) (p4 q0 q1 q2)))).symm).trans ((((cg (fun t => t ◇ ((q3 ◇ ((q2 ◇ q0) ◇ (q1 ◇ q2))) ◇ ((q1 ◇ q0) ◇ q3))) ((h q0 q1 q2).symm)).symm).trans ((h ((q2 ◇ q0) ◇ (q1 ◇ q2)) (q1 ◇ q0) q3).symm)).trans (p4 q0 q1 q2))
  have p8 : forall (q0 q1 q2:G), (q0 ◇ (q0 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0)))) = ((q0 ◇ q0) ◇ (q1 ◇ q0)):=by
    intro q0 q1 q2
    exact (p3 q0 q1 q2).trans (p4 q0 q1 q2)
  have p9 : forall (q0 q1 q2:G), (((q1 ◇ q0) ◇ (q1 ◇ q0)) ◇ (q1 ◇ (q1 ◇ q0))) = ((q2 ◇ (q1 ◇ q0)) ◇ (q1 ◇ q2)):=by
    intro q0 q1 q2
    exact ((p2 q0 q1 (q1 ◇ q0)).symm).trans (((cg (fun t => t ◇ q0) (cg (fun t => ((q1 ◇ q0) ◇ q0) ◇ t) (p4 (q1 ◇ q0) q1 q2))).symm).trans (p2 q0 q1 q2))
  have pa : forall (q0 q1 q2:G), ((q2 ◇ (q1 ◇ q0)) ◇ (q1 ◇ q2)) = ((q0 ◇ (q1 ◇ q0)) ◇ (q1 ◇ q0)):=by
    intro q0 q1 q2
    exact ((p9 q0 q1 q2).symm).trans (p9 q0 q1 q0)
  have pb : forall (q0 q2 q1:G), ((q2 ◇ (q2 ◇ q0)) ◇ ((q0 ◇ (q2 ◇ q0)) ◇ (q2 ◇ q0))) = (q2 ◇ q0):=by
    intro q0 q2 q1
    exact ((cg (fun t => (q2 ◇ (q2 ◇ q0)) ◇ t) (pa q0 q2 q1)).symm).trans (((cg (fun t => (q2 ◇ (q2 ◇ q0)) ◇ t) (p9 q0 q2 q1)).symm).trans ((h (q2 ◇ q0) q2 (q2 ◇ q0)).symm))
  have pc : forall (q0 q1 q2 q3:G), ((q3 ◇ (q1 ◇ q2)) ◇ (((q0 ◇ q0) ◇ (q1 ◇ q0)) ◇ (q3 ◇ (q2 ◇ q0)))) = (q1 ◇ q2):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => (q3 ◇ (q1 ◇ q2)) ◇ t) (cg (fun t => t ◇ (q3 ◇ (q2 ◇ q0))) (p4 q0 q1 q2))).symm).trans ((h (q1 ◇ q2) q3 (q2 ◇ q0)).symm)
  have pd : forall (q0 q1 q3 q2:G), ((((q0 ◇ q0) ◇ (q1 ◇ q0)) ◇ q3) ◇ q0) = ((q3 ◇ q3) ◇ ((q1 ◇ q0) ◇ q3)):=by
    intro q0 q1 q3 q2
    exact ((cg (fun t => t ◇ q0) (cg (fun t => t ◇ q3) (p4 q0 q1 q2))).symm).trans (((cg (fun t => (((q2 ◇ q0) ◇ (q1 ◇ q2)) ◇ q3) ◇ t) ((h q0 q1 q2).symm)).symm).trans (p4 q3 (q1 ◇ q0) ((q2 ◇ q0) ◇ (q1 ◇ q2))))
  have pe : forall (q0 q1 q2 q3:G), (((q0 ◇ q0) ◇ (q1 ◇ q0)) ◇ ((q3 ◇ (q1 ◇ q2)) ◇ ((q2 ◇ q0) ◇ q3))) = (q1 ◇ q2):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => t ◇ ((q3 ◇ (q1 ◇ q2)) ◇ ((q2 ◇ q0) ◇ q3))) (p4 q0 q1 q2)).symm).trans ((h (q1 ◇ q2) (q2 ◇ q0) q3).symm)
  have pf : forall (q0 q1 q2:G), (((q1 ◇ (q2 ◇ q0)) ◇ (q2 ◇ (q0 ◇ q1))) ◇ (q2 ◇ q0)) = (q2 ◇ (q0 ◇ q1)):=by
    intro q0 q1 q2
    exact ((cg (fun t => ((q1 ◇ (q2 ◇ q0)) ◇ (q2 ◇ (q0 ◇ q1))) ◇ t) (pe q1 q2 q0 q1)).symm).trans (pc q1 q2 (q0 ◇ q1) (q1 ◇ (q2 ◇ q0)))
  have pg : forall (q0 q1 q2 q3:G), (q1 ◇ ((((q1 ◇ q1) ◇ (q2 ◇ q1)) ◇ ((q0 ◇ q1) ◇ (q2 ◇ q0))) ◇ q1)) = ((q0 ◇ q1) ◇ (q2 ◇ q0)):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => t ◇ q1) (cg (fun t => t ◇ ((q0 ◇ q1) ◇ (q2 ◇ q0))) (p4 q1 q2 q3)))).symm).trans (((cg (fun t => t ◇ ((((q3 ◇ q1) ◇ (q2 ◇ q3)) ◇ ((q0 ◇ q1) ◇ (q2 ◇ q0))) ◇ q1)) ((h q1 q2 q0).symm)).symm).trans (p0 q1 q2 q3 ((q0 ◇ q1) ◇ (q2 ◇ q0))))
  have ph : forall (q0 q1 q2:G), (((q1 ◇ (q0 ◇ q1)) ◇ (q0 ◇ q1)) ◇ ((q1 ◇ q1) ◇ ((q1 ◇ (q0 ◇ q1)) ◇ (q0 ◇ q1)))) = q1:=by
    intro q0 q1 q2
    exact (((cg (fun t => ((q1 ◇ (q0 ◇ q1)) ◇ (q0 ◇ q1)) ◇ t) (p4 q1 ((q1 ◇ q1) ◇ ((q1 ◇ (q0 ◇ q1)) ◇ q1)) q2)).trans (cg (fun t => ((q1 ◇ (q0 ◇ q1)) ◇ (q0 ◇ q1)) ◇ t) (cg (fun t => (q1 ◇ q1) ◇ t) (p6 q0 q1)))).symm).trans (((cg (fun t => t ◇ ((q2 ◇ q1) ◇ (((q1 ◇ q1) ◇ ((q1 ◇ (q0 ◇ q1)) ◇ q1)) ◇ q2))) (p6 q0 q1)).symm).trans ((h q1 ((q1 ◇ q1) ◇ ((q1 ◇ (q0 ◇ q1)) ◇ q1)) q2).symm))
  have pi : forall (q0 q1 q3 q2:G), ((((q0 ◇ q0) ◇ (q1 ◇ q0)) ◇ ((q1 ◇ q0) ◇ q3)) ◇ q0) = ((q3 ◇ ((q1 ◇ q0) ◇ q3)) ◇ ((q1 ◇ q0) ◇ q3)):=by
    intro q0 q1 q3 q2
    exact ((cg (fun t => t ◇ q0) (cg (fun t => t ◇ ((q1 ◇ q0) ◇ q3)) (p4 q0 q1 q2))).symm).trans (((cg (fun t => (((q2 ◇ q0) ◇ (q1 ◇ q2)) ◇ ((q1 ◇ q0) ◇ q3)) ◇ t) ((h q0 q1 q2).symm)).symm).trans (pa q3 (q1 ◇ q0) ((q2 ◇ q0) ◇ (q1 ◇ q2))))
  have pj : forall (q0:G), ((q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ (q0 ◇ q0)) = ((q0 ◇ q0) ◇ (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ q0)):=by
    intro q0
    exact ((cg (fun t => t ◇ (q0 ◇ q0)) (cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) (p5 q0 q0))).symm).trans (((cg (fun t => t ◇ (q0 ◇ q0)) (pi q0 q0 (q0 ◇ q0) q0)).symm).trans (pd (q0 ◇ q0) (q0 ◇ q0) q0 q0))
  have pk : forall (q0 q1 q2 q3:G), (((q2 ◇ q1) ◇ ((q0 ◇ (q2 ◇ q3)) ◇ ((q3 ◇ q1) ◇ q0))) ◇ ((q2 ◇ q3) ◇ q1)) = ((q0 ◇ (q2 ◇ q3)) ◇ ((q3 ◇ q1) ◇ q0)):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => ((q2 ◇ q1) ◇ ((q0 ◇ (q2 ◇ q3)) ◇ ((q3 ◇ q1) ◇ q0))) ◇ t) (cg (fun t => t ◇ q1) ((h (q2 ◇ q3) (q3 ◇ q1) q0).symm))).symm).trans (p0 q1 q2 q3 ((q0 ◇ (q2 ◇ q3)) ◇ ((q3 ◇ q1) ◇ q0)))
  have pl : forall (q0 q1 q2:G), ((q2 ◇ ((q2 ◇ q1) ◇ q2)) ◇ ((q2 ◇ q1) ◇ q2)) = ((q0 ◇ ((q2 ◇ q1) ◇ q2)) ◇ ((q2 ◇ q1) ◇ q0)):=by
    intro q0 q1 q2
    exact ((pk q2 q1 (q2 ◇ q1) q2).symm).trans (((cg (fun t => t ◇ (((q2 ◇ q1) ◇ q2) ◇ q1)) (cg (fun t => ((q2 ◇ q1) ◇ q1) ◇ t) (pa q2 (q2 ◇ q1) q0))).symm).trans (pk q0 q1 (q2 ◇ q1) q2))
  have pm : forall (q0 q1 q2 q3:G), ((q1 ◇ ((q3 ◇ q2) ◇ q3)) ◇ ((q3 ◇ q2) ◇ q1)) = ((q0 ◇ ((q3 ◇ q2) ◇ q3)) ◇ ((q3 ◇ q2) ◇ q0)):=by
    intro q0 q1 q2 q3
    exact (((pl q0 q2 q3).symm).trans (pl q1 q2 q3)).symm
  have pn : forall (q0 q1 q3 q4 q2:G), ((q4 ◇ (q0 ◇ (q1 ◇ q0))) ◇ (q0 ◇ q4)) = ((q3 ◇ (q0 ◇ (q1 ◇ q0))) ◇ (q0 ◇ q3)):=by
    intro q0 q1 q3 q4 q2
    exact (((cg (fun t => (q4 ◇ (q0 ◇ (q1 ◇ q0))) ◇ t) (cg (fun t => t ◇ q4) (cg (fun t => (q1 ◇ q0) ◇ t) (p4 q0 q1 q2)))).trans (cg (fun t => (q4 ◇ (q0 ◇ (q1 ◇ q0))) ◇ t) (cg (fun t => t ◇ q4) (p5 q0 q1)))).symm).trans ((((cg (fun t => t ◇ (((q1 ◇ q0) ◇ ((q2 ◇ q0) ◇ (q1 ◇ q2))) ◇ q4)) (cg (fun t => q4 ◇ t) (cg (fun t => t ◇ (q1 ◇ q0)) ((h q0 q1 q2).symm)))).symm).trans (pm q3 q4 ((q2 ◇ q0) ◇ (q1 ◇ q2)) (q1 ◇ q0))).trans ((((cg (fun t => t ◇ (((q1 ◇ q0) ◇ ((q2 ◇ q0) ◇ (q1 ◇ q2))) ◇ q3)) (cg (fun t => q3 ◇ t) (cg (fun t => t ◇ (q1 ◇ q0)) (cg (fun t => (q1 ◇ q0) ◇ t) (p4 q0 q1 q2))))).trans (cg (fun t => (q3 ◇ (((q1 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) ◇ (q1 ◇ q0))) ◇ t) (cg (fun t => t ◇ q3) (cg (fun t => (q1 ◇ q0) ◇ t) (p4 q0 q1 q2))))).trans (cg (fun t => t ◇ (((q1 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) ◇ q3)) (cg (fun t => q3 ◇ t) (cg (fun t => t ◇ (q1 ◇ q0)) (p5 q0 q1))))).trans (cg (fun t => (q3 ◇ (q0 ◇ (q1 ◇ q0))) ◇ t) (cg (fun t => t ◇ q3) (p5 q0 q1)))))
  have po : forall (q0 q1 q2 q3 q4:G), ((q3 ◇ (q0 ◇ (q1 ◇ q0))) ◇ (q0 ◇ q3)) = ((q0 ◇ (q0 ◇ (q1 ◇ q0))) ◇ (q0 ◇ q0)):=by
    intro q0 q1 q2 q3 q4
    exact ((pn q0 q1 q3 q4 q2).symm).trans (pn q0 q1 q0 q4 q2)
  have pp : forall (q0 q1 q2 q3 q4:G), ((q4 ◇ ((q0 ◇ q2) ◇ (q1 ◇ q0))) ◇ (q2 ◇ q4)) = ((q3 ◇ ((q0 ◇ q2) ◇ (q1 ◇ q0))) ◇ (q2 ◇ q3)):=by
    intro q0 q1 q2 q3 q4
    exact (((cg (fun t => t ◇ (q2 ◇ q4)) (cg (fun t => q4 ◇ t) (pg q0 q2 q1 q0))).symm).trans (pn q2 (((q2 ◇ q2) ◇ (q1 ◇ q2)) ◇ ((q0 ◇ q2) ◇ (q1 ◇ q0))) q3 q4 q0)).trans (cg (fun t => t ◇ (q2 ◇ q3)) (cg (fun t => q3 ◇ t) (pg q0 q2 q1 (q2 ◇ ((((q2 ◇ q2) ◇ (q1 ◇ q2)) ◇ ((q0 ◇ q2) ◇ (q1 ◇ q0))) ◇ q2)))))
  have pq : forall (q0 q1 q2 q3:G), ((q3 ◇ ((q0 ◇ q2) ◇ (q1 ◇ q0))) ◇ (q2 ◇ q3)) = (q2 ◇ (q2 ◇ (q1 ◇ q2))):=by
    intro q0 q1 q2 q3
    exact (((cg (fun t => t ◇ (q2 ◇ (q1 ◇ q2))) ((h q2 q1 q0).symm)).symm).trans (pp q0 q1 q2 q3 (q1 ◇ q2))).symm
  have pr : forall (q0 q1 q2:G), ((q2 ◇ ((q0 ◇ q2) ◇ (q1 ◇ q0))) ◇ (q2 ◇ (q2 ◇ (q1 ◇ q2)))) = ((q0 ◇ q2) ◇ (q1 ◇ q0)):=by
    intro q0 q1 q2
    exact ((cg (fun t => (q2 ◇ ((q0 ◇ q2) ◇ (q1 ◇ q0))) ◇ t) (pq q0 q1 q2 q0)).symm).trans ((h ((q0 ◇ q2) ◇ (q1 ◇ q0)) q2 q0).symm)
  have ps : forall (q0 q1 q2 q3:G), (((q0 ◇ q0) ◇ ((q1 ◇ q3) ◇ q0)) ◇ (q3 ◇ ((q2 ◇ q1) ◇ q0))) = (q3 ◇ (q3 ◇ (q2 ◇ q3))):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => t ◇ (q3 ◇ ((q2 ◇ q1) ◇ q0))) (p4 q0 (q1 ◇ q3) (q2 ◇ q1))).symm).trans (pq q1 q2 q3 ((q2 ◇ q1) ◇ q0))
  have pt : forall (q0 q1 q2 q3:G), ((q0 ◇ q0) ◇ (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ q0)) = (q0 ◇ (q0 ◇ (q0 ◇ q0))):=by
    intro q0 q1 q2 q3
    exact (((pq q0 q0 q0 q0).symm).trans (pj q0)).symm
  have pu : forall (q0:G), ((q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0)))) = ((q0 ◇ q0) ◇ q0):=by
    intro q0
    exact ((cg (fun t => t ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0)))) (pt q0 ((q0 ◇ q0) ◇ (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ q0)) ((q0 ◇ q0) ◇ (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ q0)) ((q0 ◇ q0) ◇ (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ q0)))).symm).trans ((((cg (fun t => ((q0 ◇ q0) ◇ (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ q0)) ◇ t) (pt q0 q0 q0 q0)).symm).trans (ps q0 (q0 ◇ q0) (q0 ◇ q0) (q0 ◇ q0))).trans (cg (fun t => (q0 ◇ q0) ◇ t) (p5 q0 q0)))
  have pv : forall (q0:G), (((q0 ◇ q0) ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0)))) ◇ q0) = (q0 ◇ (q0 ◇ (q0 ◇ q0))):=by
    intro q0
    exact (((cg (fun t => t ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0)))) (cg (fun t => t ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0)))) (cg (fun t => q0 ◇ t) (p5 q0 q0)))).trans (cg (fun t => ((q0 ◇ q0) ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0)))) ◇ t) (p5 q0 q0))).symm).trans ((((cg (fun t => t ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0)))) (cg (fun t => (q0 ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0)))) ◇ t) (pt q0 q0 q0 q0))).symm).trans (pf ((q0 ◇ q0) ◇ (q0 ◇ q0)) q0 (q0 ◇ q0))).trans (pt q0 ((q0 ◇ q0) ◇ (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ q0)) ((q0 ◇ q0) ◇ (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ q0)) ((q0 ◇ q0) ◇ (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ q0))))
  have pw : forall (q0 q1:G), ((q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ ((q0 ◇ q0) ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0))))) = q0:=by
    intro q0 q1
    exact (((cg (fun t => (q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ t) (p4 q0 ((q0 ◇ q0) ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0)))) q1)).trans (cg (fun t => (q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (pv q0)))).symm).trans (((cg (fun t => t ◇ ((q1 ◇ q0) ◇ (((q0 ◇ q0) ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0)))) ◇ q1))) (pv q0)).symm).trans ((h q0 ((q0 ◇ q0) ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0)))) q1).symm))
  have px : forall (q0:G), ((q0 ◇ q0) ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0)))) = (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))):=by
    intro q0
    exact ((((cg (fun t => q0 ◇ t) (cg (fun t => q0 ◇ t) (cg (fun t => (q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ t) (pv q0)))).trans (cg (fun t => q0 ◇ t) (cg (fun t => q0 ◇ t) (pu q0)))).symm).trans ((((cg (fun t => q0 ◇ t) (cg (fun t => q0 ◇ t) (cg (fun t => t ◇ (((q0 ◇ q0) ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0)))) ◇ q0)) (pv q0)))).symm).trans (p8 q0 ((q0 ◇ q0) ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0)))) q0)).trans (cg (fun t => (q0 ◇ q0) ◇ t) (pv q0)))).symm
  have py : forall (q0 q1:G), ((q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0)))) = q0:=by
    intro q0 q1
    exact ((cg (fun t => (q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ t) (px q0)).symm).trans (pw q0 q1)
  have pz : forall (q0:G), (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0)) = (((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)):=by
    intro q0
    exact (((cg (fun t => ((q0 ◇ q0) ◇ q0) ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (p5 q0 q0))).symm).trans (((cg (fun t => t ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))))) (cg (fun t => (q0 ◇ q0) ◇ t) ((h q0 q0 q0).symm))).symm).trans (pu (q0 ◇ q0)))).symm
  have p10 : forall (q0 q1 q2:G), ((((q1 ◇ q2) ◇ ((q1 ◇ q0) ◇ (q2 ◇ q0))) ◇ q0) ◇ ((q1 ◇ q0) ◇ (q2 ◇ q0))) = q0:=by
    intro q0 q1 q2
    exact (((cg (fun t => t ◇ ((q1 ◇ q0) ◇ (q2 ◇ q0))) (cg (fun t => ((q1 ◇ q2) ◇ ((q1 ◇ q0) ◇ (q2 ◇ q0))) ◇ t) ((h q0 q1 q2).symm))).symm).trans (pf (q2 ◇ q0) (q1 ◇ q2) (q1 ◇ q0))).trans ((cg (fun t => (q1 ◇ q0) ◇ t) (p4 q0 q1 q2)).trans (p5 q0 q1))
  have p11 : forall (q0 q1:G), ((((q1 ◇ (q0 ◇ (q1 ◇ q0))) ◇ (q1 ◇ q0)) ◇ (q1 ◇ q0)) ◇ (q1 ◇ q0)) = (q1 ◇ q0):=by
    intro q0 q1
    exact ((cg (fun t => (((q1 ◇ (q0 ◇ (q1 ◇ q0))) ◇ (q1 ◇ q0)) ◇ (q1 ◇ q0)) ◇ t) (pb q0 q1 ((q1 ◇ (q1 ◇ q0)) ◇ ((q0 ◇ (q1 ◇ q0)) ◇ (q1 ◇ q0))))).symm).trans (((cg (fun t => t ◇ ((q1 ◇ (q1 ◇ q0)) ◇ ((q0 ◇ (q1 ◇ q0)) ◇ (q1 ◇ q0)))) (cg (fun t => t ◇ (q1 ◇ q0)) (cg (fun t => (q1 ◇ (q0 ◇ (q1 ◇ q0))) ◇ t) ((h (q1 ◇ q0) q1 q0).symm)))).symm).trans (p10 (q1 ◇ q0) q1 (q0 ◇ (q1 ◇ q0))))
  have p12 : forall (q0 q1:G), ((q1 ◇ q0) ◇ (((q1 ◇ q0) ◇ (q1 ◇ q0)) ◇ (q1 ◇ q0))) = (q1 ◇ q0):=by
    intro q0 q1
    exact ((cg (fun t => (q1 ◇ q0) ◇ t) (cg (fun t => ((q1 ◇ q0) ◇ (q1 ◇ q0)) ◇ t) (p11 q0 q1))).symm).trans (((cg (fun t => t ◇ (((q1 ◇ q0) ◇ (q1 ◇ q0)) ◇ ((((q1 ◇ (q0 ◇ (q1 ◇ q0))) ◇ (q1 ◇ q0)) ◇ (q1 ◇ q0)) ◇ (q1 ◇ q0)))) (p11 q0 q1)).symm).trans (p5 (q1 ◇ q0) (((q1 ◇ (q0 ◇ (q1 ◇ q0))) ◇ (q1 ◇ q0)) ◇ (q1 ◇ q0))))
  have p13 : forall (q0:G), ((q0 ◇ q0) ◇ (((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))) = (q0 ◇ q0):=by
    intro q0
    exact ((cg (fun t => (q0 ◇ q0) ◇ t) (pz q0)).symm).trans (p12 q0 q0)
  have p14 : forall (q0:G), ((q0 ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))) = (q0 ◇ q0):=by
    intro q0
    exact ((cg (fun t => t ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))) (cg (fun t => t ◇ (q0 ◇ q0)) (p5 q0 (q0 ◇ q0)))).symm).trans ((((cg (fun t => t ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))) (cg (fun t => (((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))) ◇ t) (p13 q0))).symm).trans (pf ((q0 ◇ q0) ◇ q0) ((q0 ◇ q0) ◇ q0) (q0 ◇ q0))).trans (p13 q0))
  have p15 : forall (q0:G), ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) = (q0 ◇ q0):=by
    intro q0
    exact ((((cg (fun t => q0 ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (p4 q0 q0 (q0 ◇ q0)))).trans (cg (fun t => q0 ◇ t) (p5 q0 q0))).symm).trans (((cg (fun t => q0 ◇ t) (cg (fun t => t ◇ (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ (q0 ◇ q0)))) (p14 q0))).symm).trans (p7 q0 (q0 ◇ q0) (q0 ◇ (q0 ◇ q0)) q0))).symm
  have p16 : forall (q0 q1:G), ((q0 ◇ ((q1 ◇ q1) ◇ q1)) ◇ ((q1 ◇ q1) ◇ q0)) = q1:=by
    intro q0 q1
    exact (((p5 q1 q1).symm).trans (((cg (fun t => t ◇ ((q1 ◇ q1) ◇ (q1 ◇ q1))) (p15 q1)).symm).trans (pm q0 (q1 ◇ q1) q1 q1))).symm
  have p17 : forall (q0:G), (q0 ◇ ((q0 ◇ q0) ◇ q0)) = q0:=by
    intro q0
    exact ((cg (fun t => q0 ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (p16 q0 q0))).symm).trans (((cg (fun t => t ◇ ((q0 ◇ q0) ◇ ((q0 ◇ ((q0 ◇ q0) ◇ q0)) ◇ ((q0 ◇ q0) ◇ q0)))) (p16 q0 q0)).symm).trans (ph (q0 ◇ q0) q0 q0))
  have p18 : forall (q0 q1:G), ((q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ (q0 ◇ q0)) = q0:=by
    intro q0 q1
    exact ((cg (fun t => (q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ t) (cg (fun t => q0 ◇ t) (p17 q0))).symm).trans (py q0 q1)
  have p19 : forall (q0 q1:G), ((q0 ◇ q1) ◇ ((q1 ◇ q1) ◇ q0)) = (q1 ◇ q1):=by
    intro q0 q1
    exact ((((pq q0 (q1 ◇ q1) q1 q1).trans (cg (fun t => q1 ◇ t) (p17 q1))).symm).trans (((cg (fun t => (q1 ◇ ((q0 ◇ q1) ◇ ((q1 ◇ q1) ◇ q0))) ◇ t) (cg (fun t => q1 ◇ t) (p17 q1))).symm).trans (pr q0 (q1 ◇ q1) q1))).symm
  have p1a : forall (q0:G), ((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ (q0 ◇ q0))) = q0:=by
    intro q0
    exact ((((po q0 q0 (((q0 ◇ q0) ◇ (q0 ◇ (q0 ◇ q0))) ◇ (q0 ◇ (q0 ◇ q0))) (q0 ◇ q0) (((q0 ◇ q0) ◇ (q0 ◇ (q0 ◇ q0))) ◇ (q0 ◇ (q0 ◇ q0)))).trans (p18 q0 ((q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ (q0 ◇ q0)))).symm).trans (((cg (fun t => ((q0 ◇ q0) ◇ (q0 ◇ (q0 ◇ q0))) ◇ t) (pf q0 q0 q0)).symm).trans (p19 (q0 ◇ q0) (q0 ◇ (q0 ◇ q0))))).symm
  have p1b : forall (q0 q1:G), ((((q1 ◇ q1) ◇ q0) ◇ ((q1 ◇ q1) ◇ q0)) ◇ (q1 ◇ q1)) = q0:=by
    intro q0 q1
    exact (((((cg (fun t => ((q1 ◇ q1) ◇ q0) ◇ t) (cg (fun t => ((q1 ◇ q1) ◇ q0) ◇ t) (cg (fun t => (q1 ◇ q1) ◇ t) (p19 q0 q1)))).trans (cg (fun t => ((q1 ◇ q1) ◇ q0) ◇ t) (p4 q0 (q1 ◇ q1) (q1 ◇ q1)))).trans (p5 q0 (q1 ◇ q1))).symm).trans ((((cg (fun t => ((q1 ◇ q1) ◇ q0) ◇ t) (cg (fun t => ((q1 ◇ q1) ◇ q0) ◇ t) (cg (fun t => t ◇ ((q0 ◇ q1) ◇ ((q1 ◇ q1) ◇ q0))) (p19 q0 q1)))).symm).trans (p8 ((q1 ◇ q1) ◇ q0) (q0 ◇ q1) q0)).trans (cg (fun t => (((q1 ◇ q1) ◇ q0) ◇ ((q1 ◇ q1) ◇ q0)) ◇ t) (p19 q0 q1)))).symm
  have p1c : forall (q0 q1:G), (((q0 ◇ q1) ◇ (q0 ◇ q1)) ◇ q0) = q1:=by
    intro q0 q1
    exact (((cg (fun t => t ◇ ((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ (q0 ◇ q0)))) (cg (fun t => (q0 ◇ q1) ◇ t) (cg (fun t => t ◇ q1) (p1a q0)))).trans (cg (fun t => ((q0 ◇ q1) ◇ (q0 ◇ q1)) ◇ t) (p1a q0))).symm).trans (((cg (fun t => t ◇ ((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ (q0 ◇ q0)))) (cg (fun t => t ◇ (((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ (q0 ◇ q0))) ◇ q1)) (cg (fun t => t ◇ q1) (p1a q0)))).symm).trans (p1b q1 (q0 ◇ (q0 ◇ q0))))
  have p1d : forall (q0 q1 q2:G), (q0 ◇ ((q1 ◇ q1) ◇ q0)) = q1:=by
    intro q0 q1 q2
    exact (((cg (fun t => q0 ◇ t) (p4 q1 ((q1 ◇ q0) ◇ (q1 ◇ q0)) q2)).trans (cg (fun t => q0 ◇ t) (cg (fun t => (q1 ◇ q1) ◇ t) (p1c q1 q0)))).symm).trans (((cg (fun t => t ◇ ((q2 ◇ q1) ◇ (((q1 ◇ q0) ◇ (q1 ◇ q0)) ◇ q2))) (p1c q1 q0)).symm).trans ((h q1 ((q1 ◇ q0) ◇ (q1 ◇ q0)) q2).symm))
  have p1e : forall (q0 q1:G), (((q0 ◇ q0) ◇ (q1 ◇ q1)) ◇ q0) = q1:=by
    intro q0 q1
    exact ((cg (fun t => ((q0 ◇ q0) ◇ (q1 ◇ q1)) ◇ t) (p1d (q1 ◇ q1) q0 q0)).symm).trans (p1d ((q0 ◇ q0) ◇ (q1 ◇ q1)) q1 q0)
  have p1f : forall (q0 q1:G), ((q0 ◇ q0) ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) = q1:=by
    intro q0 q1
    exact ((cg (fun t => t ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) (cg (fun t => q0 ◇ t) (p1c q1 q0))).symm).trans (((cg (fun t => t ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) (cg (fun t => t ◇ (((q1 ◇ q0) ◇ (q1 ◇ q0)) ◇ q1)) (p1c q1 q0))).symm).trans (p1c ((q1 ◇ q0) ◇ (q1 ◇ q0)) q1))
  have p1g : forall (q0 q1:G), (q0 ◇ ((q1 ◇ q1) ◇ q1)) = q0:=by
    intro q0 q1
    exact ((((cg (fun t => (((q1 ◇ q1) ◇ q0) ◇ ((q1 ◇ q1) ◇ q0)) ◇ t) (cg (fun t => q1 ◇ t) (p16 q0 q1))).trans (p1c (q1 ◇ q1) q0)).symm).trans (((cg (fun t => (((q1 ◇ q1) ◇ q0) ◇ ((q1 ◇ q1) ◇ q0)) ◇ t) (cg (fun t => t ◇ ((q0 ◇ ((q1 ◇ q1) ◇ q1)) ◇ ((q1 ◇ q1) ◇ q0))) (p16 q0 q1))).symm).trans (p1f ((q1 ◇ q1) ◇ q0) (q0 ◇ ((q1 ◇ q1) ◇ q1))))).symm
  have p1h : forall (q0 q1:G), (((q0 ◇ q0) ◇ q0) ◇ (q1 ◇ q1)) = q1:=by
    intro q0 q1
    exact ((cg (fun t => t ◇ (q1 ◇ q1)) (p1g ((q0 ◇ q0) ◇ q0) q0)).symm).trans (((p1g ((((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ (q1 ◇ q1)) q0).symm).trans (p1e ((q0 ◇ q0) ◇ q0) q1))
  have p1i : forall (q0 q1:G), (((q1 ◇ q1) ◇ q0) ◇ (q1 ◇ q0)) = q0:=by
    intro q0 q1
    exact ((cg (fun t => ((q1 ◇ q1) ◇ q0) ◇ t) (p1g (q1 ◇ q0) q1)).symm).trans ((h q0 (q1 ◇ q1) q1).symm)
  have p1j : forall (q0 q1:G), (q0 ◇ ((q1 ◇ q0) ◇ q1)) = q1:=by
    intro q0 q1
    exact ((cg (fun t => t ◇ ((q1 ◇ q0) ◇ q1)) (p1c q1 q0)).symm).trans (p1i q1 (q1 ◇ q0))
  have p1k : forall (q0 q1:G), ((q0 ◇ q1) ◇ q0) = ((q0 ◇ q0) ◇ q1):=by
    intro q0 q1
    exact (((cg (fun t => t ◇ q1) (cg (fun t => q0 ◇ t) (p1j q1 q0))).symm).trans (((cg (fun t => t ◇ q1) (cg (fun t => t ◇ (q1 ◇ ((q0 ◇ q1) ◇ q0))) (p1j q1 q0))).symm).trans (p1c q1 ((q0 ◇ q1) ◇ q0)))).symm
  have p1l : forall (q0 q1 q2 q3:G), ((q3 ◇ q2) ◇ (((q3 ◇ ((q0 ◇ q3) ◇ (q0 ◇ q3))) ◇ q2) ◇ ((q1 ◇ q3) ◇ (q0 ◇ q1)))) = q2:=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => (q3 ◇ q2) ◇ t) (cg (fun t => ((q3 ◇ ((q0 ◇ q3) ◇ (q0 ◇ q3))) ◇ q2) ◇ t) (p3 q3 q0 q1))).symm).trans ((h q2 q3 (q3 ◇ ((q0 ◇ q3) ◇ (q0 ◇ q3)))).symm)
  have p1m : forall (q0 q1 q2:G), ((q0 ◇ ((q1 ◇ q2) ◇ (q0 ◇ q1))) ◇ q2) = q2:=by
    intro q0 q1 q2
    exact (((cg (fun t => t ◇ q2) (cg (fun t => t ◇ ((q1 ◇ q2) ◇ (q0 ◇ q1))) (p1k q2 ((q0 ◇ q2) ◇ (q0 ◇ q2))))).trans (cg (fun t => t ◇ q2) (cg (fun t => t ◇ ((q1 ◇ q2) ◇ (q0 ◇ q1))) (p1f q2 q0)))).symm).trans (((cg (fun t => (((q2 ◇ ((q0 ◇ q2) ◇ (q0 ◇ q2))) ◇ q2) ◇ ((q1 ◇ q2) ◇ (q0 ◇ q1))) ◇ t) (p1l q0 q1 q2 q2)).symm).trans (p1d (((q2 ◇ ((q0 ◇ q2) ◇ (q0 ◇ q2))) ◇ q2) ◇ ((q1 ◇ q2) ◇ (q0 ◇ q1))) q2 q0))
  have p1n : forall (q0 q1 q2:G), ((q1 ◇ ((((q0 ◇ q0) ◇ q1) ◇ q2) ◇ q0)) ◇ q2) = q2:=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ q2) (cg (fun t => q1 ◇ t) (cg (fun t => (((q0 ◇ q0) ◇ q1) ◇ q2) ◇ t) (p1d q1 q0 q0)))).symm).trans (p1m q1 ((q0 ◇ q0) ◇ q1) q2)
  have p1o : forall (q0 q1 q2:G), ((q1 ◇ ((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ q2)) ◇ q2) = q2:=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ q2) (cg (fun t => q1 ◇ t) (cg (fun t => t ◇ q2) (cg (fun t => t ◇ q1) (p1g ((q0 ◇ q0) ◇ q0) q0))))).symm).trans (((cg (fun t => t ◇ q2) (cg (fun t => q1 ◇ t) (p1g (((((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ q1) ◇ q2) q0))).symm).trans (p1n ((q0 ◇ q0) ◇ q0) q1 q2))
  have p1p : forall (q0 q1 q2:G), (((q0 ◇ (q1 ◇ q1)) ◇ (((q1 ◇ q1) ◇ (q0 ◇ q1)) ◇ q2)) ◇ q2) = q2:=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ q2) (cg (fun t => (q0 ◇ (q1 ◇ q1)) ◇ t) (cg (fun t => t ◇ q2) (p4 q1 q0 (q1 ◇ q1))))).symm).trans (p1o q1 (q0 ◇ (q1 ◇ q1)) q2)
  have p1q : forall (q0 q1 q2:G), ((q1 ◇ (((q1 ◇ q1) ◇ (((q0 ◇ q0) ◇ q0) ◇ q1)) ◇ q2)) ◇ q2) = q2:=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ q2) (cg (fun t => t ◇ (((q1 ◇ q1) ◇ (((q0 ◇ q0) ◇ q0) ◇ q1)) ◇ q2)) (p1h q0 q1))).symm).trans (p1p ((q0 ◇ q0) ◇ q0) q1 q2)
  have p1r : forall (q0 q1 q2:G), ((q1 ◇ (((q0 ◇ q1) ◇ (((q1 ◇ q1) ◇ q1) ◇ q0)) ◇ q2)) ◇ q2) = q2:=by
    intro q0 q1 q2
    exact (((cg (fun t => t ◇ q2) (cg (fun t => (((q1 ◇ q1) ◇ q1) ◇ (q1 ◇ q1)) ◇ t) (cg (fun t => t ◇ q2) (cg (fun t => t ◇ (((q1 ◇ q1) ◇ q1) ◇ q0)) (cg (fun t => q0 ◇ t) (p1h q1 q1)))))).trans (cg (fun t => t ◇ q2) (cg (fun t => t ◇ (((q0 ◇ q1) ◇ (((q1 ◇ q1) ◇ q1) ◇ q0)) ◇ q2)) (p1h q1 q1)))).symm).trans (((cg (fun t => t ◇ q2) (cg (fun t => (((q1 ◇ q1) ◇ q1) ◇ (q1 ◇ q1)) ◇ t) (cg (fun t => t ◇ q2) (pm q0 (((q1 ◇ q1) ◇ q1) ◇ (q1 ◇ q1)) q1 (q1 ◇ q1))))).symm).trans (p1q q1 (((q1 ◇ q1) ◇ q1) ◇ (q1 ◇ q1)) q2))
  have p1s : forall (q0 q1 q2:G), ((q1 ◇ ((q0 ◇ (q1 ◇ q0)) ◇ q2)) ◇ q2) = q2:=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ q2) (cg (fun t => q1 ◇ t) (cg (fun t => t ◇ q2) (cg (fun t => q0 ◇ t) (p1h q1 (q1 ◇ q0)))))).symm).trans (((cg (fun t => t ◇ q2) (cg (fun t => q1 ◇ t) (cg (fun t => t ◇ q2) (cg (fun t => t ◇ (((q1 ◇ q1) ◇ q1) ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0)))) (p1c q1 q0))))).symm).trans (p1r ((q1 ◇ q0) ◇ (q1 ◇ q0)) q1 q2))
  exact (calc
    x = x:=rfl
    _ = ((y ◇ ((z ◇ (y ◇ z)) ◇ x)) ◇ x):=(p1s z y x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_19010_to_32498 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_19010_to_32498
