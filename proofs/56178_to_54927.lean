-- Equation56178 → Equation54927
-- Recorded verdict: true
-- Premise: x ◇ (y ◇ z) = (y ◇ z) ◇ (x ◇ y)
-- Conclusion: x ◇ (y ◇ x) = y ◇ ((x ◇ y) ◇ x)
-- Original submission SHA-256: 6dde5e0074077b99aaaddf62a0b043ea64e28eb145bf43dd5fa318b3c2e477c1
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ z) = (y ◇ z) ◇ (x ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ (y ◇ x) = y ◇ ((x ◇ y) ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have p0 : forall (q0 q1 q2 q3:G), ((q0 ◇ (q1 ◇ q2)) ◇ (q3 ◇ (q1 ◇ q2))) = (q3 ◇ ((q1 ◇ q2) ◇ (q0 ◇ q1))):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => t ◇ (q3 ◇ (q1 ◇ q2))) ((h q0 q1 q2).symm)).symm).trans ((h q3 (q1 ◇ q2) (q0 ◇ q1)).symm)
  have p1 : forall (q0 q1 q2 q3:G), (((q0 ◇ q1) ◇ q3) ◇ (q0 ◇ (q1 ◇ q2))) = ((q1 ◇ q2) ◇ ((q0 ◇ q1) ◇ q3)):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => ((q0 ◇ q1) ◇ q3) ◇ t) ((h q0 q1 q2).symm)).symm).trans ((h (q1 ◇ q2) (q0 ◇ q1) q3).symm)
  have p2 : forall (q0 q1:G), ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q1)) = (q0 ◇ ((q0 ◇ q0) ◇ q1)):=by
    intro q0 q1
    exact ((p1 q0 q0 q0 q1).symm).trans ((h q0 (q0 ◇ q0) q1).symm)
  have p3 : forall (q0:G), ((q0 ◇ q0) ◇ (q0 ◇ q0)) = (q0 ◇ ((q0 ◇ q0) ◇ q0)):=by
    intro q0
    exact (((p2 q0 q0).symm).trans ((h (q0 ◇ q0) q0 q0).symm)).symm
  have p4 : forall (q0:G), (q0 ◇ ((q0 ◇ q0) ◇ q0)) = (q0 ◇ (q0 ◇ q0)):=by
    intro q0
    exact ((p3 q0).symm).trans ((h q0 q0 q0).symm)
  have p5 : forall (q0:G), ((q0 ◇ q0) ◇ (q0 ◇ q0)) = (q0 ◇ (q0 ◇ q0)):=by
    intro q0
    exact (p3 q0).trans (p4 q0)
  have p6 : forall (q0 q1:G), ((q1 ◇ q1) ◇ (q0 ◇ (q1 ◇ q1))) = (q1 ◇ ((q1 ◇ q1) ◇ (q0 ◇ q1))):=by
    intro q0 q1
    exact ((cg (fun t => (q1 ◇ q1) ◇ t) ((h q0 q1 q1).symm)).symm).trans (p2 q1 (q0 ◇ q1))
  have p7 : forall (q0 q1:G), ((q1 ◇ (q1 ◇ q1)) ◇ (q0 ◇ q1)) = (q0 ◇ (q1 ◇ (q1 ◇ q1))):=by
    intro q0 q1
    exact (((cg (fun t => t ◇ (q0 ◇ q1)) (p4 q1)).symm).trans ((h q0 q1 ((q1 ◇ q1) ◇ q1)).symm)).trans (cg (fun t => q0 ◇ t) (p4 q1))
  have p8 : forall (q0 q1 q2 q3:G), ((q3 ◇ q0) ◇ ((q2 ◇ q3) ◇ (q1 ◇ q2))) = ((q1 ◇ (q2 ◇ q3)) ◇ (q2 ◇ (q3 ◇ q0))):=by
    intro q0 q1 q2 q3
    exact (((cg (fun t => (q1 ◇ (q2 ◇ q3)) ◇ t) ((h q2 q3 q0).symm)).symm).trans (p0 q1 q2 q3 (q3 ◇ q0))).symm
  have p9 : forall (q0 q1 q2 q3:G), ((q1 ◇ (q2 ◇ q3)) ◇ (q2 ◇ (q3 ◇ q0))) = ((q3 ◇ q0) ◇ (q1 ◇ (q2 ◇ q3))):=by
    intro q0 q1 q2 q3
    exact (((cg (fun t => (q3 ◇ q0) ◇ t) ((h q1 q2 q3).symm)).symm).trans (p8 q0 q1 q2 q3)).symm
  have pa : forall (q0 q1 q2 q3 q4:G), ((q3 ◇ ((q1 ◇ q2) ◇ (q0 ◇ q1))) ◇ (q4 ◇ (q0 ◇ (q1 ◇ q2)))) = (q4 ◇ (q3 ◇ ((q1 ◇ q2) ◇ (q0 ◇ q1)))):=by
    intro q0 q1 q2 q3 q4
    exact (((cg (fun t => t ◇ (q4 ◇ (q0 ◇ (q1 ◇ q2)))) (p0 q0 q1 q2 q3)).symm).trans ((h q4 (q0 ◇ (q1 ◇ q2)) (q3 ◇ (q1 ◇ q2))).symm)).trans (cg (fun t => q4 ◇ t) (p0 q0 q1 q2 q3))
  have pb : forall (q0 q1 q2 q3:G), ((q3 ◇ q0) ◇ ((q2 ◇ q3) ◇ (q1 ◇ q2))) = ((q3 ◇ q0) ◇ (q1 ◇ (q2 ◇ q3))):=by
    intro q0 q1 q2 q3
    exact (p8 q0 q1 q2 q3).trans (p9 q0 q1 q2 q3)
  have pc : forall (q0 q1 q2:G), ((q1 ◇ q0) ◇ ((q1 ◇ q0) ◇ (q2 ◇ q1))) = (q2 ◇ ((q1 ◇ q0) ◇ (q2 ◇ q1))):=by
    intro q0 q1 q2
    exact ((p9 q0 (q1 ◇ q0) q2 q1).symm).trans ((h q2 (q1 ◇ q0) (q2 ◇ q1)).symm)
  have pd : forall (q0 q1 q2:G), (q2 ◇ ((q1 ◇ q0) ◇ (q2 ◇ q1))) = ((q1 ◇ q0) ◇ (q2 ◇ (q1 ◇ q0))):=by
    intro q0 q1 q2
    exact (((cg (fun t => (q1 ◇ q0) ◇ t) ((h q2 q1 q0).symm)).symm).trans (pc q0 q1 q2)).symm
  have pe : forall (q0 q1 q2:G), ((q1 ◇ q0) ◇ (q2 ◇ (q1 ◇ q0))) = (q2 ◇ (q2 ◇ (q1 ◇ q0))):=by
    intro q0 q1 q2
    exact (((cg (fun t => q2 ◇ t) ((h q2 q1 q0).symm)).symm).trans (pd q0 q1 q2)).symm
  have pf : forall (q0 q1 q2:G), (q2 ◇ ((q1 ◇ q0) ◇ (q2 ◇ q1))) = (q2 ◇ (q2 ◇ (q1 ◇ q0))):=by
    intro q0 q1 q2
    exact (pd q0 q1 q2).trans (pe q0 q1 q2)
  have pg : forall (q0 q1 q2:G), (q1 ◇ ((q1 ◇ q1) ◇ (q0 ◇ q1))) = (q0 ◇ (q0 ◇ (q1 ◇ q1))):=by
    intro q0 q1 q2
    exact (((pe q1 q1 q0).symm).trans (p6 q0 q1)).symm
  have ph : forall (q0 q1:G), (q1 ◇ (q0 ◇ (q1 ◇ q1))) = (q0 ◇ (q0 ◇ (q1 ◇ q1))):=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) ((h q0 q1 q1).symm)).symm).trans (pg q0 q1 q0)
  have pi : forall (q0 q1 q2 q3 q4:G), (((q1 ◇ q2) ◇ (q0 ◇ q1)) ◇ ((q3 ◇ (q1 ◇ q2)) ◇ q4)) = ((q0 ◇ (q1 ◇ q2)) ◇ ((q3 ◇ (q1 ◇ q2)) ◇ q4)):=by
    intro q0 q1 q2 q3 q4
    exact ((p1 q3 (q1 ◇ q2) (q0 ◇ q1) q4).symm).trans (((cg (fun t => ((q3 ◇ (q1 ◇ q2)) ◇ q4) ◇ t) (p0 q0 q1 q2 q3)).symm).trans ((h (q0 ◇ (q1 ◇ q2)) (q3 ◇ (q1 ◇ q2)) q4).symm))
  have pj : forall (q0 q1 q2 q3:G), (q3 ◇ ((q1 ◇ q2) ◇ ((q2 ◇ q0) ◇ q1))) = ((q1 ◇ (q2 ◇ q0)) ◇ (q3 ◇ (q1 ◇ q2))):=by
    intro q0 q1 q2 q3
    exact (((cg (fun t => t ◇ (q3 ◇ (q1 ◇ q2))) ((h q1 q2 q0).symm)).symm).trans (p0 (q2 ◇ q0) q1 q2 q3)).symm
  have pk : forall (q0 q1 q2 q3:G), ((q1 ◇ (q2 ◇ q0)) ◇ (q3 ◇ (q1 ◇ q2))) = (q3 ◇ ((q2 ◇ q0) ◇ (q1 ◇ q2))):=by
    intro q0 q1 q2 q3
    exact (((cg (fun t => q3 ◇ t) ((h (q2 ◇ q0) q1 q2).symm)).symm).trans (pj q0 q1 q2 q3)).symm
  have pl : forall (q0 q1 q2:G), (q2 ◇ ((q0 ◇ q1) ◇ ((q2 ◇ q0) ◇ q0))) = ((q0 ◇ q1) ◇ ((q2 ◇ q0) ◇ (q0 ◇ q1))):=by
    intro q0 q1 q2
    exact (((p1 q2 q0 q1 (q0 ◇ q1)).symm).trans (p0 (q2 ◇ q0) q0 q1 q2)).symm
  have pm : forall (q0 q1 q2:G), ((q0 ◇ q1) ◇ ((q2 ◇ q0) ◇ (q0 ◇ q1))) = (q2 ◇ ((q2 ◇ q0) ◇ (q0 ◇ q1))):=by
    intro q0 q1 q2
    exact (((cg (fun t => q2 ◇ t) ((h (q2 ◇ q0) q0 q1).symm)).symm).trans (pl q0 q1 q2)).symm
  have pn : forall (q0 q1:G), (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))) = ((q0 ◇ q1) ◇ (q0 ◇ (q1 ◇ q0))):=by
    intro q0 q1
    exact (((cg (fun t => (q0 ◇ q1) ◇ t) ((h q0 q1 q0).symm)).symm).trans (pm q0 q1 q1)).symm
  have po : forall (q0 q1:G), ((q0 ◇ q1) ◇ (q0 ◇ (q1 ◇ q0))) = (q1 ◇ (q0 ◇ (q1 ◇ q0))):=by
    intro q0 q1
    exact (((cg (fun t => q1 ◇ t) ((h q0 q1 q0).symm)).symm).trans (pn q0 q1)).symm
  have pp : forall (q0 q1 q2 q3:G), ((q3 ◇ q1) ◇ ((q3 ◇ q0) ◇ (q2 ◇ q3))) = ((q2 ◇ (q3 ◇ q0)) ◇ (q2 ◇ (q3 ◇ q1))):=by
    intro q0 q1 q2 q3
    exact (((cg (fun t => t ◇ (q2 ◇ (q3 ◇ q1))) ((h q2 q3 q0).symm)).symm).trans (p9 q1 (q3 ◇ q0) q2 q3)).symm
  have pq : forall (q0 q1 q2 q3:G), ((q2 ◇ (q3 ◇ q0)) ◇ (q2 ◇ (q3 ◇ q1))) = ((q3 ◇ q1) ◇ (q2 ◇ (q3 ◇ q0))):=by
    intro q0 q1 q2 q3
    exact (((cg (fun t => (q3 ◇ q1) ◇ t) ((h q2 q3 q0).symm)).symm).trans (pp q0 q1 q2 q3)).symm
  have pr : forall (q0 q1 q2 q3:G), ((q3 ◇ q1) ◇ ((q3 ◇ q0) ◇ (q2 ◇ q3))) = ((q3 ◇ q1) ◇ (q2 ◇ (q3 ◇ q0))):=by
    intro q0 q1 q2 q3
    exact (pp q0 q1 q2 q3).trans (pq q0 q1 q2 q3)
  have ps : forall (q0 q1 q2:G), ((q2 ◇ q1) ◇ (q2 ◇ (q1 ◇ q0))) = (q2 ◇ (q2 ◇ (q1 ◇ q0))):=by
    intro q0 q1 q2
    exact (((cg (fun t => (q2 ◇ q1) ◇ t) ((h q2 q1 q0).symm)).symm).trans (pe q1 q2 (q1 ◇ q0))).trans ((pr q0 q0 q2 q1).trans (pe q0 q1 q2))
  have pt : forall (q0 q1 q2:G), (q1 ◇ (q0 ◇ (q1 ◇ q0))) = (q0 ◇ (q0 ◇ (q1 ◇ q0))):=by
    intro q0 q1 q2
    exact (((ps q0 q1 q0).symm).trans (po q0 q1)).symm
  have pu : forall (q0:G), (q0 ◇ (q0 ◇ (q0 ◇ q0))) = (q0 ◇ (q0 ◇ q0)):=by
    intro q0
    exact (((((p1 q0 q0 q0 q0).trans (p2 q0 q0)).trans (p4 q0)).symm).trans ((((cg (fun t => ((q0 ◇ q0) ◇ q0) ◇ t) (p4 q0)).symm).trans (pe q0 (q0 ◇ q0) q0)).trans (cg (fun t => q0 ◇ t) (p4 q0)))).symm
  have pv : forall (q0 q1:G), (q0 ◇ (q0 ◇ (q1 ◇ (q0 ◇ q1)))) = (q1 ◇ (q1 ◇ (q0 ◇ q1))):=by
    intro q0 q1
    exact (((pe (q0 ◇ q1) q1 q0).symm).trans (p9 (q0 ◇ q1) q1 q0 q1)).trans ((p0 q1 q0 q1 q1).trans (pf q1 q0 q1))
  have pw : forall (q0 q1:G), (q0 ◇ (q1 ◇ (q1 ◇ (q0 ◇ q1)))) = (q1 ◇ (q1 ◇ (q0 ◇ q1))):=by
    intro q0 q1
    exact ((cg (fun t => q0 ◇ t) (pt q1 q0 q0)).symm).trans (pv q0 q1)
  have px : forall (q0 q1 q2 q3 q4:G), (((q3 ◇ (q1 ◇ q2)) ◇ q4) ◇ (q3 ◇ (q0 ◇ (q1 ◇ q2)))) = ((q0 ◇ (q1 ◇ q2)) ◇ ((q3 ◇ (q1 ◇ q2)) ◇ q4)):=by
    intro q0 q1 q2 q3 q4
    exact (((cg (fun t => ((q3 ◇ (q1 ◇ q2)) ◇ q4) ◇ t) (cg (fun t => q3 ◇ t) ((h q0 q1 q2).symm))).symm).trans (p1 q3 (q1 ◇ q2) (q0 ◇ q1) q4)).trans (pi q0 q1 q2 q3 q4)
  have py : forall (q0 q1 q2 q3:G), ((q2 ◇ (q0 ◇ q1)) ◇ ((q2 ◇ (q0 ◇ q1)) ◇ q3)) = (q2 ◇ ((q2 ◇ (q0 ◇ q1)) ◇ q3)):=by
    intro q0 q1 q2 q3
    exact ((px q2 q0 q1 q2 q3).symm).trans ((h q2 (q2 ◇ (q0 ◇ q1)) q3).symm)
  have pz : forall (q0 q1 q2:G), ((q0 ◇ (q0 ◇ (q2 ◇ q2))) ◇ (q1 ◇ q2)) = (q1 ◇ (q0 ◇ (q0 ◇ (q2 ◇ q2)))):=by
    intro q0 q1 q2
    exact (((cg (fun t => t ◇ (q1 ◇ q2)) (ph q0 q2)).symm).trans ((h q1 q2 (q0 ◇ (q2 ◇ q2))).symm)).trans (cg (fun t => q1 ◇ t) (ph q0 q2))
  have p10 : forall (q0 q1 q2:G), ((q0 ◇ (q0 ◇ (q2 ◇ q0))) ◇ (q1 ◇ q2)) = (q1 ◇ (q0 ◇ (q0 ◇ (q2 ◇ q0)))):=by
    intro q0 q1 q2
    exact (((cg (fun t => t ◇ (q1 ◇ q2)) (pt q0 q2 q0)).symm).trans ((h q1 q2 (q0 ◇ (q2 ◇ q0))).symm)).trans (cg (fun t => q1 ◇ t) (pt q0 q2 (q2 ◇ (q0 ◇ (q2 ◇ q0)))))
  have p11 : forall (q0 q1:G), ((q1 ◇ (q1 ◇ q1)) ◇ ((q1 ◇ q1) ◇ (q1 ◇ q0))) = ((q1 ◇ q0) ◇ (q1 ◇ (q1 ◇ q1))):=by
    intro q0 q1
    exact (((cg (fun t => t ◇ ((q1 ◇ q1) ◇ (q1 ◇ q0))) (p4 q1)).symm).trans (p9 q0 q1 (q1 ◇ q1) q1)).trans (cg (fun t => (q1 ◇ q0) ◇ t) (p4 q1))
  have p12 : forall (q0 q1:G), ((q0 ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ q1)) = (q0 ◇ ((q0 ◇ q0) ◇ q1)):=by
    intro q0 q1
    exact ((((p1 q0 q0 q0 q1).trans (p2 q0 q1)).symm).trans (((cg (fun t => ((q0 ◇ q0) ◇ q1) ◇ t) (pu q0)).symm).trans (p1 q0 q0 (q0 ◇ q0) q1))).symm
  have p13 : forall (q0 q1:G), ((q1 ◇ q0) ◇ (q1 ◇ (q1 ◇ q1))) = (q1 ◇ ((q1 ◇ q1) ◇ (q1 ◇ q0))):=by
    intro q0 q1
    exact (((p12 q1 (q1 ◇ q0)).symm).trans (p11 q0 q1)).symm
  have p14 : forall (q0 q1:G), (q0 ◇ (q1 ◇ (q1 ◇ q1))) = (q0 ◇ (q0 ◇ (q1 ◇ q1))):=by
    intro q0 q1
    exact ((((p0 q0 q1 q1 q1).trans (pg q0 q1 (q1 ◇ ((q1 ◇ q1) ◇ (q0 ◇ q1))))).symm).trans ((((cg (fun t => (q0 ◇ (q1 ◇ q1)) ◇ t) (pu q1)).symm).trans (p9 (q1 ◇ q1) q0 q1 q1)).trans ((p0 q1 q1 q1 q0).trans (cg (fun t => q0 ◇ t) (p5 q1))))).symm
  have p15 : forall (q0 q1:G), ((q1 ◇ (q1 ◇ q1)) ◇ (q0 ◇ q1)) = (q0 ◇ (q0 ◇ (q1 ◇ q1))):=by
    intro q0 q1
    exact (p7 q0 q1).trans (p14 q0 q1)
  have p16 : forall (q0 q1:G), ((q1 ◇ q0) ◇ (q1 ◇ (q1 ◇ q1))) = (q1 ◇ (q1 ◇ (q1 ◇ q0))):=by
    intro q0 q1
    exact ((((pk q0 q1 q1 q1).trans (pf q0 q1 q1)).symm).trans ((((cg (fun t => (q1 ◇ (q1 ◇ q0)) ◇ t) (pu q1)).symm).trans (pq q0 (q1 ◇ q1) q1 q1)).trans (p9 q0 q1 q1 q1))).symm
  have p17 : forall (q0 q1:G), (q1 ◇ ((q1 ◇ q1) ◇ (q1 ◇ q0))) = (q1 ◇ (q1 ◇ (q1 ◇ q0))):=by
    intro q0 q1
    exact (((p16 q0 q1).symm).trans (p13 q0 q1)).symm
  have p18 : forall (q0 q1 q2:G), (q2 ◇ (q1 ◇ (q1 ◇ (q0 ◇ q0)))) = (q2 ◇ (q1 ◇ (q0 ◇ (q0 ◇ q0)))):=by
    intro q0 q1 q2
    exact (((((cg (fun t => (q1 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ t) (cg (fun t => q2 ◇ t) (p5 q0))).trans (cg (fun t => t ◇ (q2 ◇ (q0 ◇ (q0 ◇ q0)))) (cg (fun t => q1 ◇ t) (p4 q0)))).trans (p0 q1 q0 (q0 ◇ q0) q2)).trans (cg (fun t => q2 ◇ t) (p15 q1 q0))).symm).trans ((((cg (fun t => t ◇ (q2 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0)))) (cg (fun t => q1 ◇ t) (p3 q0))).symm).trans (p0 q1 (q0 ◇ q0) (q0 ◇ q0) q2)).trans (((cg (fun t => q2 ◇ t) (cg (fun t => t ◇ (q1 ◇ (q0 ◇ q0))) (p5 q0))).trans (cg (fun t => q2 ◇ t) (p0 q0 q0 q0 q1))).trans (cg (fun t => q2 ◇ t) (cg (fun t => q1 ◇ t) (p5 q0)))))
  have p19 : forall (q0 q1 q2:G), (((q0 ◇ q1) ◇ q2) ◇ (q0 ◇ (q0 ◇ (q1 ◇ q1)))) = ((q1 ◇ (q1 ◇ q1)) ◇ ((q0 ◇ q1) ◇ q2)):=by
    intro q0 q1 q2
    exact ((cg (fun t => ((q0 ◇ q1) ◇ q2) ◇ t) (p14 q0 q1)).symm).trans (((cg (fun t => ((q0 ◇ q1) ◇ q2) ◇ t) (p7 q0 q1)).symm).trans ((h (q1 ◇ (q1 ◇ q1)) (q0 ◇ q1) q2).symm))
  have p1a : forall (q0 q1 q2:G), ((q0 ◇ (q0 ◇ (q1 ◇ q1))) ◇ (q2 ◇ (q1 ◇ (q1 ◇ q1)))) = (q2 ◇ (q0 ◇ (q0 ◇ (q1 ◇ q1)))):=by
    intro q0 q1 q2
    exact (((cg (fun t => (q0 ◇ (q1 ◇ (q1 ◇ q1))) ◇ t) (cg (fun t => q2 ◇ t) (p4 q1))).trans (cg (fun t => t ◇ (q2 ◇ (q1 ◇ (q1 ◇ q1)))) (p14 q0 q1))).symm).trans ((((cg (fun t => t ◇ (q2 ◇ (q1 ◇ ((q1 ◇ q1) ◇ q1)))) (cg (fun t => q0 ◇ t) (p4 q1))).symm).trans (p0 q0 q1 ((q1 ◇ q1) ◇ q1) q2)).trans ((cg (fun t => q2 ◇ t) (cg (fun t => t ◇ (q0 ◇ q1)) (p4 q1))).trans (cg (fun t => q2 ◇ t) (p15 q0 q1))))
  have p1b : forall (q0 q1:G), (q1 ◇ (q1 ◇ (q0 ◇ (q0 ◇ q0)))) = (q1 ◇ (q0 ◇ (q0 ◇ q0))):=by
    intro q0 q1
    exact ((pe (q0 ◇ q0) q0 q1).symm).trans ((((cg (fun t => t ◇ (q1 ◇ (q0 ◇ (q0 ◇ q0)))) (pu q0)).symm).trans (p1a q0 q0 q1)).trans (cg (fun t => q1 ◇ t) (pu q0)))
  have p1c : forall (q0 q1:G), ((q0 ◇ q0) ◇ (q1 ◇ (q0 ◇ (q0 ◇ q0)))) = (q1 ◇ (q0 ◇ (q0 ◇ q0))):=by
    intro q0 q1
    exact (((cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => q1 ◇ t) ((h q0 q0 q0).symm))).symm).trans (ph q1 (q0 ◇ q0))).trans ((cg (fun t => q1 ◇ t) (cg (fun t => q1 ◇ t) (p5 q0))).trans (p1b q0 q1))
  have p1d : forall (q0 q1 q2:G), ((q1 ◇ q1) ◇ ((q0 ◇ (q1 ◇ q1)) ◇ q2)) = (q0 ◇ ((q0 ◇ (q1 ◇ q1)) ◇ q2)):=by
    intro q0 q1 q2
    exact (((((cg (fun t => ((q0 ◇ (q1 ◇ q1)) ◇ q2) ◇ t) (pg q0 q1 (q1 ◇ ((q1 ◇ q1) ◇ (q0 ◇ q1))))).trans (px q0 q1 q1 q0 q2)).trans (py q1 q1 q0 q2)).symm).trans (((cg (fun t => ((q0 ◇ (q1 ◇ q1)) ◇ q2) ◇ t) (p6 q0 q1)).symm).trans ((h (q1 ◇ q1) (q0 ◇ (q1 ◇ q1)) q2).symm))).symm
  have p1e : forall (q0 q1:G), (q0 ◇ (q0 ◇ (q0 ◇ (q1 ◇ q1)))) = (q0 ◇ (q0 ◇ (q1 ◇ q1))):=by
    intro q0 q1
    exact (((cg (fun t => q0 ◇ t) (p0 q0 q1 q1 q1)).trans (cg (fun t => q0 ◇ t) (pg q0 q1 (q1 ◇ ((q1 ◇ q1) ◇ (q0 ◇ q1)))))).symm).trans ((((p1d q0 q1 (q1 ◇ (q1 ◇ q1))).symm).trans (p1c q1 (q0 ◇ (q1 ◇ q1)))).trans ((p0 q0 q1 q1 q1).trans (pg q0 q1 (q1 ◇ ((q1 ◇ q1) ◇ (q0 ◇ q1))))))
  have p1f : forall (q0 q1 q2 q3:G), ((q2 ◇ (q2 ◇ (q1 ◇ q0))) ◇ (q3 ◇ (q1 ◇ q0))) = (q3 ◇ (q2 ◇ (q2 ◇ (q1 ◇ q0)))):=by
    intro q0 q1 q2 q3
    exact (((cg (fun t => t ◇ (q3 ◇ (q1 ◇ q0))) (pe q0 q1 q2)).symm).trans ((h q3 (q1 ◇ q0) (q2 ◇ (q1 ◇ q0))).symm)).trans (cg (fun t => q3 ◇ t) (pe q0 q1 q2))
  have p1g : forall (q0 q1:G), (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q1))) = (q0 ◇ ((q0 ◇ q0) ◇ q1)):=by
    intro q0 q1
    exact ((ps q1 (q0 ◇ q0) q0).symm).trans ((((cg (fun t => t ◇ (q0 ◇ ((q0 ◇ q0) ◇ q1))) (p4 q0)).symm).trans (pq q0 q1 q0 (q0 ◇ q0))).trans (((cg (fun t => ((q0 ◇ q0) ◇ q1) ◇ t) (p4 q0)).trans (p1 q0 q0 q0 q1)).trans (p2 q0 q1)))
  have p1h : forall (q0 q1 q2:G), (((q0 ◇ q1) ◇ q2) ◇ (q1 ◇ (q1 ◇ (q0 ◇ q1)))) = ((q1 ◇ (q0 ◇ q1)) ◇ ((q0 ◇ q1) ◇ q2)):=by
    intro q0 q1 q2
    exact ((cg (fun t => ((q0 ◇ q1) ◇ q2) ◇ t) (pt q1 q0 q0)).symm).trans (p1 q0 q1 (q0 ◇ q1) q2)
  have p1i : forall (q0 q1 q2:G), ((q0 ◇ (q1 ◇ q2)) ◇ (q2 ◇ (q2 ◇ (q1 ◇ q2)))) = (q0 ◇ ((q1 ◇ q2) ◇ (q2 ◇ q1))):=by
    intro q0 q1 q2
    exact (((cg (fun t => (q0 ◇ (q1 ◇ q2)) ◇ t) (pt q2 q1 q0)).symm).trans (p9 (q1 ◇ q2) q0 q1 q2)).trans (p0 q2 q1 q2 q0)
  have p1j : forall (q0 q1 q2:G), (q2 ◇ ((q1 ◇ (q0 ◇ q1)) ◇ (q0 ◇ q1))) = (q2 ◇ (q1 ◇ (q1 ◇ (q0 ◇ q1)))):=by
    intro q0 q1 q2
    exact (((p1f q1 q0 q1 q2).symm).trans (((cg (fun t => t ◇ (q2 ◇ (q0 ◇ q1))) (pt q1 q0 q0)).symm).trans (pk (q0 ◇ q1) q0 q1 q2))).symm
  have p1k : forall (q0 q1 q2 q3:G), (q3 ◇ ((q0 ◇ (q1 ◇ q2)) ◇ (q0 ◇ q0))) = (q3 ◇ (q0 ◇ (q0 ◇ (q1 ◇ q2)))):=by
    intro q0 q1 q2 q3
    exact ((p0 q0 q0 (q1 ◇ q2) q3).symm).trans ((((cg (fun t => t ◇ (q3 ◇ (q0 ◇ (q1 ◇ q2)))) (pf q2 q1 q0)).symm).trans (pa q0 q1 q2 q0 q3)).trans (cg (fun t => q3 ◇ t) (pf q2 q1 q0)))
  have p1l : forall (q0 q1 q2:G), ((q2 ◇ q1) ◇ (q2 ◇ (q2 ◇ (q1 ◇ q0)))) = (q2 ◇ (q2 ◇ (q2 ◇ (q1 ◇ q0)))):=by
    intro q0 q1 q2
    exact (((pe (q1 ◇ q0) q2 q2).symm).trans ((((cg (fun t => (q2 ◇ (q1 ◇ q0)) ◇ t) (ps q0 q1 q2)).symm).trans (pe (q1 ◇ q0) q2 (q2 ◇ q1))).trans (cg (fun t => (q2 ◇ q1) ◇ t) (ps q0 q1 q2)))).symm
  have p1m : forall (q0 q1 q2:G), (((q2 ◇ q1) ◇ q2) ◇ (q2 ◇ (q2 ◇ (q1 ◇ q0)))) = (q2 ◇ (q2 ◇ (q2 ◇ (q1 ◇ q0)))):=by
    intro q0 q1 q2
    exact (((cg (fun t => ((q2 ◇ q1) ◇ q2) ◇ t) (ps q0 q1 q2)).symm).trans (ps (q1 ◇ q0) q2 (q2 ◇ q1))).trans ((cg (fun t => (q2 ◇ q1) ◇ t) (ps q0 q1 q2)).trans (p1l q0 q1 q2))
  have p1n : forall (q0 q1:G), ((q0 ◇ (q0 ◇ q0)) ◇ ((q1 ◇ q0) ◇ q1)) = (q1 ◇ (q0 ◇ (q0 ◇ q0))):=by
    intro q0 q1
    exact ((p1 q1 q0 (q0 ◇ q0) q1).symm).trans ((((cg (fun t => ((q1 ◇ q0) ◇ q1) ◇ t) (p1b q0 q1)).symm).trans (p1m (q0 ◇ q0) q0 q1)).trans ((cg (fun t => q1 ◇ t) (p1b q0 q1)).trans (p1b q0 q1)))
  have p1o : forall (q0 q1 q2:G), ((q1 ◇ (q1 ◇ (q0 ◇ q1))) ◇ ((q0 ◇ q1) ◇ q2)) = ((q1 ◇ (q0 ◇ q1)) ◇ ((q0 ◇ q1) ◇ q2)):=by
    intro q0 q1 q2
    exact (((p1h q0 q1 q2).symm).trans (((cg (fun t => ((q0 ◇ q1) ◇ q2) ◇ t) (pw q0 q1)).symm).trans (p1 q0 q1 (q1 ◇ (q0 ◇ q1)) q2))).symm
  have p1p : forall (q0 q1 q2:G), (q2 ◇ ((q1 ◇ (q0 ◇ q0)) ◇ (q0 ◇ q1))) = (q2 ◇ (q1 ◇ (q0 ◇ (q0 ◇ q0)))):=by
    intro q0 q1 q2
    exact (((((p0 q1 q1 (q0 ◇ q0) q2).trans (p1k q1 q0 q0 q2)).trans (p18 q0 q1 q2)).symm).trans (((cg (fun t => t ◇ (q2 ◇ (q1 ◇ (q0 ◇ q0)))) (ph q1 q0)).symm).trans (p0 q0 q1 (q0 ◇ q0) q2))).symm
  have p1q : forall (q0 q1 q2:G), (q2 ◇ (q1 ◇ (q0 ◇ (q0 ◇ q0)))) = (q2 ◇ (q0 ◇ (q1 ◇ (q0 ◇ q0)))):=by
    intro q0 q1 q2
    exact (((cg (fun t => q2 ◇ t) ((h q0 q1 (q0 ◇ q0)).symm)).symm).trans (p1p q0 q1 q2)).symm
  have p1r : forall (q0 q1 q2:G), (q1 ◇ (q0 ◇ (q1 ◇ (q0 ◇ q0)))) = (q1 ◇ (q0 ◇ (q0 ◇ q0))):=by
    intro q0 q1 q2
    exact ((p1q q0 q1 q1).symm).trans (p1b q0 q1)
  have p1s : forall (q0 q1 q2:G), (q2 ◇ (q1 ◇ (q1 ◇ (q0 ◇ q0)))) = (q2 ◇ (q0 ◇ (q1 ◇ (q0 ◇ q0)))):=by
    intro q0 q1 q2
    exact (p18 q0 q1 q2).trans (p1q q0 q1 q2)
  have p1t : forall (q0 q1 q2:G), (q0 ◇ (q2 ◇ (q2 ◇ (q1 ◇ q2)))) = (q0 ◇ ((q1 ◇ q2) ◇ (q2 ◇ q1))):=by
    intro q0 q1 q2
    exact ((p1f q2 q1 q2 q0).symm).trans ((((cg (fun t => (q2 ◇ (q2 ◇ (q1 ◇ q2))) ◇ t) ((h q0 q1 q2).symm)).symm).trans (p1o q1 q2 (q0 ◇ q1))).trans ((pb (q1 ◇ q2) q0 q1 q2).trans (p0 q2 q1 q2 q0)))
  have p1u : forall (q0 q1 q2:G), ((q0 ◇ (q0 ◇ (q2 ◇ q0))) ◇ (q1 ◇ q2)) = (q1 ◇ ((q2 ◇ q0) ◇ (q0 ◇ q2))):=by
    intro q0 q1 q2
    exact (p10 q0 q1 q2).trans (p1t q1 q2 q0)
  have p1v : forall (q0 q1 q2:G), (q2 ◇ ((q1 ◇ (q0 ◇ q1)) ◇ (q0 ◇ q1))) = (q2 ◇ ((q0 ◇ q1) ◇ (q1 ◇ q0))):=by
    intro q0 q1 q2
    exact (p1j q0 q1 q2).trans (p1t q2 q0 q1)
  have p1w : forall (q0 q1 q2:G), (q2 ◇ ((q0 ◇ q1) ◇ (q1 ◇ q0))) = (q2 ◇ (q0 ◇ (q1 ◇ (q0 ◇ q1)))):=by
    intro q0 q1 q2
    exact (((cg (fun t => q2 ◇ t) ((h q0 q1 (q0 ◇ q1)).symm)).symm).trans (p1v q0 q1 q2)).symm
  have p1x : forall (q0 q1 q2:G), (q2 ◇ (q0 ◇ (q1 ◇ (q0 ◇ q1)))) = (q2 ◇ (q1 ◇ (q0 ◇ q1))):=by
    intro q0 q1 q2
    exact (((cg (fun t => q2 ◇ t) ((h q1 q0 q1).symm)).symm).trans (p1w q0 q1 q2)).symm
  have p1y : forall (q0 q1 q2:G), (q2 ◇ ((q0 ◇ q1) ◇ (q1 ◇ q0))) = (q2 ◇ (q1 ◇ (q0 ◇ q1))):=by
    intro q0 q1 q2
    exact (p1w q0 q1 q2).trans (p1x q0 q1 q2)
  have p1z : forall (q0 q1 q2:G), (q0 ◇ (q2 ◇ (q2 ◇ (q1 ◇ q2)))) = (q0 ◇ (q2 ◇ (q1 ◇ q2))):=by
    intro q0 q1 q2
    exact (p1t q0 q1 q2).trans (p1y q1 q2 q0)
  have p20 : forall (q0 q1 q2:G), ((q0 ◇ (q0 ◇ (q2 ◇ q0))) ◇ (q1 ◇ q2)) = (q1 ◇ (q0 ◇ (q2 ◇ q0))):=by
    intro q0 q1 q2
    exact (p1u q0 q1 q2).trans (p1y q2 q0 q1)
  have p21 : forall (q0 q1 q2:G), (q2 ◇ ((q1 ◇ q2) ◇ (q0 ◇ q1))) = (q0 ◇ (q2 ◇ (q1 ◇ q2))):=by
    intro q0 q1 q2
    exact (((p1y q1 q2 (q0 ◇ (q1 ◇ q2))).trans (p0 q0 q1 q2 q2)).symm).trans ((((p1t (q0 ◇ (q1 ◇ q2)) q1 q2).symm).trans (p1i q0 q1 q2)).trans (p1y q1 q2 q0))
  have p22 : forall (q0 q1 q2:G), (q2 ◇ (q0 ◇ (q1 ◇ q2))) = (q0 ◇ (q2 ◇ (q1 ◇ q2))):=by
    intro q0 q1 q2
    exact ((cg (fun t => q2 ◇ t) ((h q0 q1 q2).symm)).symm).trans (p21 q0 q1 q2)
  have p23 : forall (q0 q1:G), (q1 ◇ (q1 ◇ (q0 ◇ q1))) = (q0 ◇ (q0 ◇ (q1 ◇ q1))):=by
    intro q0 q1
    exact (((p17 (q0 ◇ q1) q1).trans (p1z q1 q0 q1)).symm).trans ((((cg (fun t => q1 ◇ t) (p22 (q1 ◇ q1) q0 q1)).symm).trans (p1g q1 (q0 ◇ q1))).trans ((p21 q0 q1 q1).trans (p14 q0 q1)))
  have p24 : forall (q0 q1 q2:G), (q0 ◇ (q1 ◇ (q1 ◇ (q2 ◇ q2)))) = (q0 ◇ (q2 ◇ (q1 ◇ q2))):=by
    intro q0 q1 q2
    exact ((cg (fun t => q0 ◇ t) (p23 q1 q2)).symm).trans (p1z q0 q1 q2)
  have p25 : forall (q0 q1 q2:G), (q0 ◇ (q1 ◇ (q0 ◇ q1))) = (q0 ◇ (q0 ◇ (q1 ◇ q1))):=by
    intro q0 q1 q2
    exact ((p24 q0 q0 q1).symm).trans (p1e q0 q1)
  have p26 : forall (q0 q1 q2:G), (q2 ◇ (q0 ◇ (q1 ◇ (q0 ◇ q0)))) = (q2 ◇ (q0 ◇ (q1 ◇ q0))):=by
    intro q0 q1 q2
    exact (((p24 q2 q1 q0).symm).trans (p1s q0 q1 q2)).symm
  have p27 : forall (q0 q1 q2:G), (q1 ◇ (q0 ◇ (q0 ◇ q0))) = (q0 ◇ (q0 ◇ (q1 ◇ q0))):=by
    intro q0 q1 q2
    exact (((pt q0 q1 (q1 ◇ (q0 ◇ (q1 ◇ q0)))).symm).trans (((p26 q0 q1 q1).symm).trans (p1r q0 q1 q2))).symm
  have p28 : forall (q0 q1 q2:G), ((q0 ◇ (q0 ◇ q0)) ◇ ((q1 ◇ q0) ◇ q1)) = (q0 ◇ (q0 ◇ (q1 ◇ q0))):=by
    intro q0 q1 q2
    exact (p1n q0 q1).trans (p27 q0 q1 (q1 ◇ (q0 ◇ (q0 ◇ q0))))
  have p29 : forall (q0 q1:G), (q0 ◇ (q0 ◇ (q1 ◇ q1))) = (q0 ◇ (q0 ◇ (q1 ◇ q0))):=by
    intro q0 q1
    exact (((ps q0 q1 q0).symm).trans ((((p22 (q0 ◇ q1) q1 q0).symm).trans (p1y q0 q1 q0)).trans (p25 q0 q1 (q0 ◇ (q1 ◇ (q0 ◇ q1)))))).symm
  have p2a : forall (q0 q1:G), (q0 ◇ (q1 ◇ (q1 ◇ q1))) = (q0 ◇ (q0 ◇ (q1 ◇ q0))):=by
    intro q0 q1
    exact (p14 q0 q1).trans (p29 q0 q1)
  have p2b : forall (q0 q1 q2:G), (q1 ◇ (q2 ◇ (q0 ◇ q2))) = (q1 ◇ (q0 ◇ (q2 ◇ q0))):=by
    intro q0 q1 q2
    exact ((((cg (fun t => t ◇ (q1 ◇ q2)) (p29 q0 q2)).trans (p20 q0 q1 q2)).symm).trans ((pz q0 q1 q2).trans (p24 q1 q0 q2))).symm
  have p2c : forall (q0 q1 q2:G), (q2 ◇ (q0 ◇ (q1 ◇ q2))) = (q0 ◇ (q1 ◇ (q2 ◇ q1))):=by
    intro q0 q1 q2
    exact (p22 q0 q1 q2).trans (p2b q1 q0 q2)
  have p2d : forall (q0 q1 q2:G), ((q1 ◇ q0) ◇ ((q0 ◇ q1) ◇ q2)) = (q1 ◇ ((q0 ◇ q1) ◇ q2)):=by
    intro q0 q1 q2
    exact ((p1 q0 q1 q0 q2).symm).trans (((p2b q0 ((q0 ◇ q1) ◇ q2) q1).symm).trans ((h q1 (q0 ◇ q1) q2).symm))
  have p2e : forall (q0 q1:G), (q0 ◇ ((q1 ◇ q0) ◇ q0)) = ((q1 ◇ q0) ◇ (q0 ◇ q1)):=by
    intro q0 q1
    exact ((p2d q1 q0 q0).symm).trans ((h (q1 ◇ q0) q0 q1).symm)
  have p2f : forall (q0 q1 q2:G), ((q1 ◇ (q1 ◇ q1)) ◇ ((q0 ◇ q1) ◇ q2)) = (q1 ◇ ((q0 ◇ q1) ◇ q2)):=by
    intro q0 q1 q2
    exact (((((p2b q0 ((q0 ◇ q1) ◇ q2) q1).trans (p1 q0 q1 q0 q2)).trans (p2d q0 q1 q2)).symm).trans (((p24 ((q0 ◇ q1) ◇ q2) q0 q1).symm).trans (p19 q0 q1 q2))).symm
  have p2g : forall (q0 q1 q2:G), (q0 ◇ (q0 ◇ (q1 ◇ q0))) = (q0 ◇ ((q1 ◇ q0) ◇ q1)):=by
    intro q0 q1 q2
    exact (((p2f q1 q0 q1).symm).trans (p28 q0 q1 q2)).symm
  have p2h : forall (q0 q1 q2:G), (q1 ◇ (q0 ◇ (q1 ◇ q0))) = (q0 ◇ ((q1 ◇ q0) ◇ q1)):=by
    intro q0 q1 q2
    exact (pt q0 q1 q2).trans (p2g q0 q1 (q0 ◇ (q0 ◇ (q1 ◇ q0))))
  have p2i : forall (q0 q1 q2:G), (q1 ◇ (q0 ◇ (q0 ◇ q0))) = (q0 ◇ ((q1 ◇ q0) ◇ q1)):=by
    intro q0 q1 q2
    exact (p27 q0 q1 q2).trans (p2g q0 q1 (q0 ◇ (q0 ◇ (q1 ◇ q0))))
  have p2j : forall (q0 q1 q2:G), (q0 ◇ (q1 ◇ (q1 ◇ q1))) = (q0 ◇ ((q1 ◇ q0) ◇ q1)):=by
    intro q0 q1 q2
    exact (p2a q0 q1).trans (p2g q0 q1 (q0 ◇ (q0 ◇ (q1 ◇ q0))))
  have p2k : forall (q0 q1 q2:G), (q1 ◇ ((q0 ◇ q1) ◇ q0)) = (q0 ◇ ((q1 ◇ q0) ◇ q1)):=by
    intro q0 q1 q2
    exact ((p2j q1 q0 (q1 ◇ (q0 ◇ (q0 ◇ q0)))).symm).trans (p2i q0 q1 q2)
  have p2l : forall (q0 q1:G), ((q0 ◇ q1) ◇ (q1 ◇ q0)) = (q0 ◇ ((q1 ◇ q0) ◇ q1)):=by
    intro q0 q1
    exact (((((pf q1 q0 q1).trans (p2b q0 q1 q1)).trans (p2h q0 q1 (q1 ◇ (q0 ◇ (q1 ◇ q0))))).symm).trans ((((cg (fun t => q1 ◇ t) (p2e q1 q0)).symm).trans (p2g q1 (q0 ◇ q1) q0)).trans ((((p2c ((q0 ◇ q1) ◇ q1) q0 q1).trans (p1 q0 q1 q0 q1)).trans (p2d q0 q1 q1)).trans (p2e q1 q0)))).symm
  have p2m : forall (q0 q1:G), (q0 ◇ ((q1 ◇ q0) ◇ q1)) = (q0 ◇ (q1 ◇ q0)):=by
    intro q0 q1
    exact ((p2k q0 q1 (q1 ◇ ((q0 ◇ q1) ◇ q0))).symm).trans (((p2l q1 q0).symm).trans ((h q0 q1 q0).symm))
  have p2n : forall (q0 q1 q2:G), (q1 ◇ (q0 ◇ q1)) = (q0 ◇ (q1 ◇ q0)):=by
    intro q0 q1 q2
    exact ((p2m q1 q0).symm).trans ((p2k q0 q1 q2).trans (p2m q0 q1))
  exact (calc
    (x ◇ (y ◇ x)) = (x ◇ (y ◇ x)):=rfl
    _ = (y ◇ ((x ◇ y) ◇ x)):=((p2m y x).trans (p2n x y (y ◇ (x ◇ y)))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_56178_to_54927 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_56178_to_54927
