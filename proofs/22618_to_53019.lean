-- Equation22618 → Equation53019
-- Recorded verdict: true
-- Premise: x = (y ◇ (y ◇ x)) ◇ ((z ◇ z) ◇ y)
-- Conclusion: x ◇ x = (((y ◇ y) ◇ x) ◇ x) ◇ x
-- Original submission SHA-256: 870bb1654031f447512f70405d799bc4472c41a4612a468d1853dc55881165e1
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (y ◇ x)) ◇ ((z ◇ z) ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ x = (((y ◇ y) ◇ x) ◇ x) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have cg : ∀ (f:G → G) {a b:G}, a=b → f a=f b:=by
    intro f a b p
    exact congrArg f p
  have p0:=fun (a b c d:G)=>by
    exact ((cg (fun t => t ◇ ((d ◇ d) ◇ (b ◇ (b ◇ a)))) (cg (fun t => (b ◇ (b ◇ a)) ◇ t) ((h a b c).symm))).symm).trans ((h ((c ◇ c) ◇ b) (b ◇ (b ◇ a)) d).symm)
  have p1:=fun (a b c d:G)=>by
    exact ((p0 a b c d).symm).trans (p0 a b a d)
  have p2:=fun (a b c d:G)=>by
    exact (((p1 a b c d).symm).trans (p1 b b c d)).symm
  have p3:=fun (a b c d:G)=>by
    exact ((cg (fun t => t ◇ d) (p1 a (b ◇ b) b a)).symm).trans (p1 c d (b ◇ b) a)
  have p4:=fun (a b c:G)=>by
    exact (((p3 a a b (a ◇ a)).symm).trans (p2 c (a ◇ a) a a)).symm
  have p5:=fun (a b c:G)=>by
    exact ((p4 a b c).symm).trans (p4 a a c)
  have p6:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ (b ◇ a)) ◇ t) ((p2 a b a a).symm)).symm).trans ((h a b a).symm)
  have p7:=fun (a b c:G)=>by
    exact ((cg (fun t => (b ◇ b) ◇ t) (p5 a c ((c ◇ c) ◇ (a ◇ a)))).symm).trans (((p3 a (a ◇ a) b ((c ◇ c) ◇ (a ◇ a))).symm).trans ((h (a ◇ a) (a ◇ a) c).symm))
  have p8:=fun (a b c:G)=>by
    exact (((((cg (fun t => t ◇ ((c ◇ c) ◇ (b ◇ b))) (p5 a b ((b ◇ b) ◇ (a ◇ a)))).trans (cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (p5 b c ((c ◇ c) ◇ (b ◇ b))))).trans (p7 b (a ◇ a) (((a ◇ a) ◇ (a ◇ a)) ◇ ((b ◇ b) ◇ (b ◇ b))))).symm).trans (((cg (fun t => t ◇ ((c ◇ c) ◇ (b ◇ b))) (cg (fun t => (b ◇ b) ◇ t) (p7 a b a))).symm).trans ((h ((a ◇ a) ◇ (a ◇ a)) (b ◇ b) c).symm))).symm
  have p9:=fun (a b c:G)=>by
    exact ((p8 a b c).symm).trans (p8 a a c)
  have pa:=fun (a b c:G)=>by
    exact (((((cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (p7 a a ((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a)))))).trans (cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (p5 a b ((b ◇ b) ◇ (a ◇ a))))).trans (p7 a (a ◇ a) (((a ◇ a) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ (a ◇ a))))).symm).trans ((((cg (fun t => t ◇ ((b ◇ b) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))))) (cg (fun t => t ◇ (a ◇ a)) (p7 a a a))).symm).trans (p0 (a ◇ a) (a ◇ a) c b)).trans (p5 a c ((c ◇ c) ◇ (a ◇ a))))).symm
  have pb:=fun (a b c:G)=>by
    exact ((cg (fun t => (b ◇ b) ◇ t) (pa a ((a ◇ a) ◇ (a ◇ a)) ((a ◇ a) ◇ (a ◇ a)))).symm).trans (p7 a b c)
  have pc:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ ((c ◇ c) ◇ b)) (cg (fun t => b ◇ t) (p9 a b a))).symm).trans ((h b b c).symm)
  have pd:=fun (a b c:G)=>by
    exact ((pc a (b ◇ (b ◇ (a ◇ a))) a).symm).trans (p0 (a ◇ a) b c a)
  have pe:=fun (a b:G)=>by
    exact (pd a b a).trans ((p2 a b a a).symm)
  have pf:=fun (a b c:G)=>by
    exact ((cg (fun t => ((c ◇ c) ◇ ((c ◇ c) ◇ b)) ◇ t) (p8 c a a)).symm).trans ((h b (c ◇ c) c).symm)
  have pg:=fun (a b c d:G)=>by
    exact ((cg (fun t => t ◇ ((d ◇ d) ◇ c)) (pd a c b)).symm).trans ((h (a ◇ a) c d).symm)
  have ph:=fun (a b c d:G)=>by
    exact (((cg (fun t => t ◇ ((b ◇ b) ◇ c)) (pg a b c b)).symm).trans (p2 d ((b ◇ b) ◇ c) a a)).symm
  have pi:=fun (a b c d:G)=>by
    exact ((cg (fun t => t ◇ (b ◇ b)) (cg (fun t => t ◇ ((d ◇ d) ◇ c)) (p9 a d a))).symm).trans (pf b c d)
  have pj:=fun (a b c d:G)=>by
    exact (((ph a b c d).symm).trans (ph b b c d)).symm
  have pk:=fun (a b c d:G)=>by
    exact ((cg (fun t => (c ◇ c) ◇ t) (cg (fun t => t ◇ d) (p9 a c a))).symm).trans (pj b c d a)
  have pl:=fun (a b c d:G)=>by
    exact (((cg (fun t => (b ◇ b) ◇ t) (cg (fun t => t ◇ d) (p9 a c a))).symm).trans ((pj b c d a).symm)).symm
  have pm:=fun (a b c:G)=>by
    exact (((cg (fun t => (b ◇ b) ◇ t) (p2 a c a a)).symm).trans ((pj b c c a).symm)).symm
  have pn:=fun (a b c:G)=>by
    exact ((cg (fun t => (b ◇ b) ◇ t) ((p2 b c a a).symm)).symm).trans (pj a b c a)
  have po:=fun (a b:G)=>by
    exact (pn a a b).trans ((pj a a b a).symm)
  have pp:=fun (a b c d:G)=>by
    exact ((cg (fun t => t ◇ ((d ◇ d) ◇ c)) (cg (fun t => c ◇ t) (pd a c b))).symm).trans ((h (c ◇ (a ◇ a)) c d).symm)
  have pq:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ ((c ◇ c) ◇ b)) (cg (fun t => b ◇ t) (pe a b))).symm).trans ((h (b ◇ (a ◇ a)) b c).symm)
  have pr:=fun (a b c:G)=>by
    exact (((pq a b c).symm).trans (pq b b c)).symm
  have ps:=fun (a b c d:G)=>by
    exact (((cg (fun t => ((b ◇ b) ◇ c) ◇ t) (pg a b c b)).symm).trans (pr d ((b ◇ b) ◇ c) a)).symm
  have pt:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ ((b ◇ b) ◇ a)) (pe c a)).symm).trans (((cg (fun t => t ◇ ((b ◇ b) ◇ a)) (cg (fun t => a ◇ t) (pr c a c))).symm).trans ((h (a ◇ a) a b).symm))
  have pu:=fun (a b c d:G)=>by
    exact (((ps a b c d).symm).trans (ps b b c d)).symm
  have pv:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ ((c ◇ c) ◇ b)) (cg (fun t => t ◇ b) (p9 a b a))).symm).trans (pt b c a)
  have pw:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ (b ◇ b)) ((p2 b c a a).symm)).symm).trans (pu a b c a)
  have px:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ ((a ◇ a) ◇ b)) (pv a b a)).symm).trans (p2 c ((a ◇ a) ◇ b) a a)).symm
  have py:=fun (a b:G)=>by
    exact ((pw a a b).trans ((pr a ((a ◇ a) ◇ b) a).symm)).trans (cg (fun t => ((a ◇ a) ◇ b) ◇ t) (pv a b a))
  have pz:=fun (a b:G)=>by
    exact ((py a b).symm).trans ((pw a a b).trans ((pu a a b a).symm))
  have p10:=fun (a b:G)=>by
    exact ((px a b a).symm).trans ((pj a a b a).symm)
  have p11:=fun (a b c d e f:G)=>by
    exact ((((cg (fun t => ((((a ◇ a) ◇ ((c ◇ c) ◇ b)) ◇ b) ◇ (e ◇ e)) ◇ t) (cg (fun t => (f ◇ f) ◇ t) (cg (fun t => ((a ◇ a) ◇ ((c ◇ c) ◇ b)) ◇ t) (pi a e b c)))).trans (pc e (((a ◇ a) ◇ ((c ◇ c) ◇ b)) ◇ b) f)).symm).trans (((cg (fun t => t ◇ ((f ◇ f) ◇ (((a ◇ a) ◇ ((c ◇ c) ◇ b)) ◇ (((a ◇ a) ◇ ((c ◇ c) ◇ b)) ◇ (e ◇ e))))) (cg (fun t => t ◇ (e ◇ e)) (cg (fun t => ((a ◇ a) ◇ ((c ◇ c) ◇ b)) ◇ t) (pi a e b c)))).symm).trans (p0 (e ◇ e) ((a ◇ a) ◇ ((c ◇ c) ◇ b)) d f))).symm
  have p12:=fun (a b c d:G)=>by
    exact (((p11 a b c d ((d ◇ d) ◇ ((a ◇ a) ◇ ((c ◇ c) ◇ b))) ((d ◇ d) ◇ ((a ◇ a) ◇ ((c ◇ c) ◇ b)))).symm).trans ((((cg (fun t => (d ◇ d) ◇ t) (p2 a ((c ◇ c) ◇ b) a a)).symm).trans (p11 ((c ◇ c) ◇ b) b c d a a)).trans (cg (fun t => t ◇ b) (cg (fun t => t ◇ ((c ◇ c) ◇ b)) (pv c b c))))).symm
  have p13:=fun (a b c:G)=>by
    exact ((p2 a b a a).trans ((p0 a b a c).symm)).symm
  have p14:=fun (a b c d:G)=>by
    exact ((cg (fun t => t ◇ ((d ◇ d) ◇ (b ◇ (b ◇ ((a ◇ a) ◇ b))))) ((h ((a ◇ a) ◇ b) b a).symm)).symm).trans (p0 ((a ◇ a) ◇ b) b c d)
  have p15:=fun (a b c d e:G)=>by
    exact ((((cg (fun t => t ◇ ((d ◇ d) ◇ ((a ◇ a) ◇ b))) (pv a b e)).trans (p11 d b a b ((b ◇ b) ◇ ((d ◇ d) ◇ ((a ◇ a) ◇ b))) ((b ◇ b) ◇ ((d ◇ d) ◇ ((a ◇ a) ◇ b))))).symm).trans (((cg (fun t => t ◇ ((d ◇ d) ◇ ((a ◇ a) ◇ b))) (cg (fun t => ((a ◇ a) ◇ b) ◇ t) (p14 a b e c))).symm).trans ((h ((c ◇ c) ◇ (b ◇ (b ◇ ((a ◇ a) ◇ b)))) ((a ◇ a) ◇ b) d).symm))).symm
  have p16:=fun (a b c d:G)=>by
    exact ((cg (fun t => (c ◇ c) ◇ t) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (p2 a b a a)))).symm).trans (p15 b b c d a)
  have p17:=fun (a b c d:G)=>by
    exact (((cg (fun t => t ◇ b) (cg (fun t => (d ◇ d) ◇ t) (p2 a b a a))).symm).trans ((p15 b b c d a).symm)).symm
  have p18:=fun (a b c d e:G)=>by
    exact (p15 a b d e c).trans ((p15 a b a e c).symm)
  have p19:=fun (a b c d e:G)=>by
    exact ((p18 b b ((c ◇ c) ◇ (b ◇ (b ◇ ((b ◇ b) ◇ b)))) c ((c ◇ c) ◇ (b ◇ (b ◇ ((b ◇ b) ◇ b))))).symm).trans (p17 a b c d)
  have p1a:=fun (a b c d:G)=>by
    exact (((p18 a b ((c ◇ c) ◇ (b ◇ (b ◇ ((a ◇ a) ◇ b)))) c ((c ◇ c) ◇ (b ◇ (b ◇ ((a ◇ a) ◇ b))))).symm).trans ((p16 a b c d).trans ((p16 b b b d).symm))).symm
  have p1b:=fun (a b c:G)=>by
    exact ((((cg (fun t => ((b ◇ b) ◇ ((a ◇ a) ◇ (b ◇ (b ◇ ((a ◇ a) ◇ b))))) ◇ t) (pb b c ((c ◇ c) ◇ (b ◇ b)))).trans (pi b b (b ◇ (b ◇ ((a ◇ a) ◇ b))) a)).symm).trans (((cg (fun t => t ◇ ((c ◇ c) ◇ (b ◇ b))) (cg (fun t => (b ◇ b) ◇ t) (p1a a b a a))).symm).trans ((h (b ◇ (b ◇ ((b ◇ b) ◇ b))) (b ◇ b) c).symm))).symm
  have p1c:=fun (a b:G)=>by
    exact (((p6 (b ◇ ((a ◇ a) ◇ b)) b).symm).trans (((cg (fun t => t ◇ ((b ◇ b) ◇ b)) (cg (fun t => b ◇ t) (p1b a b a))).symm).trans (p6 (b ◇ ((b ◇ b) ◇ b)) b))).symm
  have p1d:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ (((b ◇ b) ◇ ((a ◇ a) ◇ c)) ◇ c)) (p6 ((c ◇ c) ◇ c) c)).symm).trans (((cg (fun t => ((c ◇ (c ◇ ((c ◇ c) ◇ c))) ◇ ((c ◇ c) ◇ c)) ◇ t) (p17 a c a b)).symm).trans (p13 ((c ◇ c) ◇ c) c a))
  have p1e:=fun (a b c:G)=>by
    exact ((pr a b a).trans ((pp a a b c).symm)).symm
  have p1f:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ b) ((pk a a c b).symm)).symm).trans ((p12 a b c a).symm)
  have p1g:=fun (a b c d e:G)=>by
    exact ((cg (fun t => t ◇ ((e ◇ e) ◇ ((b ◇ (b ◇ a)) ◇ a))) (cg (fun t => ((b ◇ (b ◇ a)) ◇ a) ◇ t) (p0 a b c d))).symm).trans ((h ((d ◇ d) ◇ (b ◇ (b ◇ a))) ((b ◇ (b ◇ a)) ◇ a) e).symm)
  have p1h:=fun (a b c d e:G)=>by
    exact ((p1g a b c d e).symm).trans (p1g a b c a e)
  have p1i:=fun (a b c:G)=>by
    exact ((cg (fun t => (c ◇ c) ◇ t) (cg (fun t => b ◇ t) (p9 a b a))).symm).trans (p1h b b a c a)
  have p1j:=fun (a b c:G)=>by
    exact (((cg (fun t => (c ◇ c) ◇ t) (cg (fun t => (b ◇ (b ◇ a)) ◇ t) (p6 a b))).symm).trans (p1h ((b ◇ b) ◇ b) (b ◇ (b ◇ a)) a c a)).trans ((cg (fun t => (((b ◇ b) ◇ b) ◇ ((b ◇ b) ◇ b)) ◇ t) (cg (fun t => (b ◇ (b ◇ a)) ◇ t) (p6 a b))).trans (cg (fun t => t ◇ ((b ◇ (b ◇ a)) ◇ a)) (pv b b b)))
  have p1k:=fun (a b c:G)=>by
    exact ((p1j a b c).symm).trans ((p1j a b c).trans ((p1j a b a).symm))
  have p1l:=fun (a b c:G)=>by
    exact (p1j a b c).trans (p1k a b ((b ◇ b) ◇ ((b ◇ (b ◇ a)) ◇ a)))
  have p1m:=fun (a b c d e:G)=>by
    exact (((((((((cg (fun t => t ◇ ((c ◇ c) ◇ (b ◇ b))) (cg (fun t => t ◇ ((d ◇ d) ◇ (((b ◇ b) ◇ ((b ◇ b) ◇ a)) ◇ a))) (cg (fun t => (((b ◇ b) ◇ ((b ◇ b) ◇ a)) ◇ a) ◇ t) (pb b e ((e ◇ e) ◇ (b ◇ b)))))).trans (cg (fun t => t ◇ ((c ◇ c) ◇ (b ◇ b))) (cg (fun t => t ◇ ((d ◇ d) ◇ (((b ◇ b) ◇ ((b ◇ b) ◇ a)) ◇ a))) (cg (fun t => t ◇ (b ◇ b)) (p1f b a b))))).trans (cg (fun t => t ◇ ((c ◇ c) ◇ (b ◇ b))) (cg (fun t => t ◇ ((d ◇ d) ◇ (((b ◇ b) ◇ ((b ◇ b) ◇ a)) ◇ a))) (cg (fun t => t ◇ (b ◇ b)) (p1f b a a))))).trans (cg (fun t => t ◇ ((c ◇ c) ◇ (b ◇ b))) (cg (fun t => ((((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a) ◇ (b ◇ b)) ◇ t) (cg (fun t => (d ◇ d) ◇ t) (p1f b a b))))).trans (cg (fun t => t ◇ ((c ◇ c) ◇ (b ◇ b))) (cg (fun t => ((((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a) ◇ (b ◇ b)) ◇ t) (cg (fun t => (d ◇ d) ◇ t) (p1f b a a))))).trans (cg (fun t => t ◇ ((c ◇ c) ◇ (b ◇ b))) (cg (fun t => ((((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a) ◇ (b ◇ b)) ◇ t) (p1l a (a ◇ a) d)))).trans (cg (fun t => (((((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a) ◇ (b ◇ b)) ◇ ((a ◇ a) ◇ (((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a))) ◇ t) (pb b c ((c ◇ c) ◇ (b ◇ b))))).trans (cg (fun t => t ◇ (b ◇ b)) (pc b (((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a) a))).symm).trans (((cg (fun t => t ◇ ((c ◇ c) ◇ (b ◇ b))) ((p1g a (b ◇ b) e b d).symm)).symm).trans ((h ((b ◇ b) ◇ a) (b ◇ b) c).symm))
  have p1n:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ (c ◇ c)) (cg (fun t => t ◇ b) (po a b))).symm).trans (((cg (fun t => t ◇ (c ◇ c)) (cg (fun t => t ◇ b) (cg (fun t => t ◇ ((b ◇ b) ◇ b)) (p9 a b a)))).symm).trans (p1m b c a a a))
  have p1o:=fun (a b c d e:G)=>by
    exact ((cg (fun t => ((b ◇ (b ◇ a)) ◇ a) ◇ t) (p1h a b ((c ◇ c) ◇ (b ◇ (b ◇ a))) c ((c ◇ c) ◇ (b ◇ (b ◇ a))))).symm).trans (p13 a b c)
  have p1p:=fun (a b c:G)=>by
    exact (((cg (fun t => ((b ◇ b) ◇ (b ◇ (b ◇ b))) ◇ t) (p1i a b c)).trans (pv b (b ◇ (b ◇ b)) b)).symm).trans (((cg (fun t => t ◇ ((c ◇ c) ◇ (b ◇ (a ◇ a)))) (p1i a b a)).symm).trans (pv a (b ◇ (a ◇ a)) c))
  have p1q:=fun (a b c:G)=>by
    exact ((p1p a b a).symm).trans (p9 c (b ◇ (b ◇ b)) a)
  have p1r:=fun (a b c d:G)=>by
    exact (((cg (fun t => (b ◇ (a ◇ a)) ◇ t) (p1q a b c)).symm).trans (pr d (b ◇ (a ◇ a)) a)).symm
  have p1s:=fun (a b c d:G)=>by
    exact ((p1r a b c d).symm).trans (p1r a b a d)
  have p1t:=fun (a b c d:G)=>by
    exact (((cg (fun t => (d ◇ d) ◇ t) (cg (fun t => t ◇ c) (p1 a ((b ◇ b) ◇ c) b a))).symm).trans (p1j c (b ◇ b) d)).trans (cg (fun t => t ◇ (((b ◇ b) ◇ ((b ◇ b) ◇ c)) ◇ c)) (pb b b ((b ◇ b) ◇ (b ◇ b))))
  have p1u:=fun (a b:G)=>by
    exact ((cg (fun t => ((b ◇ (b ◇ b)) ◇ b) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (cg (fun t => b ◇ t) (p9 a b a)))).symm).trans (p1o b b a a a)
  have p1v:=fun (a b c d:G)=>by
    exact ((cg (fun t => t ◇ (((c ◇ c) ◇ ((b ◇ b) ◇ d)) ◇ d)) (cg (fun t => t ◇ d) (p9 a d a))).symm).trans (p1d b c d)
  have p1w:=fun (a b c:G)=>by
    exact ((cg (fun t => ((c ◇ (c ◇ c)) ◇ c) ◇ t) (cg (fun t => t ◇ (c ◇ (b ◇ b))) (p9 a c a))).symm).trans (p1u b c)
  have p1x:=fun (a b c d:G)=>by
    exact (((cg (fun t => (d ◇ d) ◇ t) (p1h a b a d a)).symm).trans (pj c d (b ◇ (b ◇ a)) a)).trans (cg (fun t => (c ◇ c) ◇ t) (p1h a b ((d ◇ d) ◇ (b ◇ (b ◇ a))) d ((d ◇ d) ◇ (b ◇ (b ◇ a)))))
  have p1y:=fun (a b c d:G)=>by
    exact ((cg (fun t => t ◇ (d ◇ d)) (cg (fun t => t ◇ c) (pl a b c c))).symm).trans (p1m c d a a a)
  have p1z:=fun (a b c d:G)=>by
    exact (((p1x d a b a).symm).trans ((pk c a d (a ◇ (a ◇ d))).symm)).symm
  have p20:=fun (a b c d:G)=>by
    exact ((((cg (fun t => ((((((a ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ b) ◇ (((a ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ b)) ◇ b) ◇ (((a ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ b)) ◇ t) (cg (fun t => (c ◇ c) ◇ t) (p1y a a b d))).trans (cg (fun t => t ◇ ((c ◇ c) ◇ ((d ◇ d) ◇ b))) (p1v (((a ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ b) a a b))).symm).trans ((((cg (fun t => t ◇ ((c ◇ c) ◇ ((((a ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ b) ◇ (d ◇ d)))) (cg (fun t => t ◇ (((a ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ b)) (p1n a b (((a ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ b)))).symm).trans (p1w c d (((a ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ b))).trans ((p1l b (a ◇ a) (((a ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ b)).trans (p1t a a b b)))).symm
  have p21:=fun (a b c d:G)=>by
    exact ((((cg (fun t => (b ◇ ((a ◇ a) ◇ ((c ◇ c) ◇ b))) ◇ t) (cg (fun t => (d ◇ d) ◇ t) (cg (fun t => ((a ◇ a) ◇ ((c ◇ c) ◇ b)) ◇ t) (pv a ((c ◇ c) ◇ b) a)))).trans (cg (fun t => (b ◇ ((a ◇ a) ◇ ((c ◇ c) ◇ b))) ◇ t) (cg (fun t => (d ◇ d) ◇ t) (cg (fun t => ((a ◇ a) ◇ ((c ◇ c) ◇ b)) ◇ t) (pv c b c))))).trans (cg (fun t => (b ◇ ((a ◇ a) ◇ ((c ◇ c) ◇ b))) ◇ t) (cg (fun t => (d ◇ d) ◇ t) (pi a b b c)))).symm).trans ((((cg (fun t => t ◇ ((d ◇ d) ◇ (((a ◇ a) ◇ ((c ◇ c) ◇ b)) ◇ (((a ◇ a) ◇ ((c ◇ c) ◇ b)) ◇ ((a ◇ a) ◇ ((c ◇ c) ◇ b)))))) (cg (fun t => t ◇ ((a ◇ a) ◇ ((c ◇ c) ◇ b))) (pi a ((a ◇ a) ◇ ((c ◇ c) ◇ b)) b c))).symm).trans (p13 ((a ◇ a) ◇ ((c ◇ c) ◇ b)) ((a ◇ a) ◇ ((c ◇ c) ◇ b)) d)).trans (((cg (fun t => t ◇ ((a ◇ a) ◇ ((c ◇ c) ◇ b))) (pv a ((c ◇ c) ◇ b) a)).trans (cg (fun t => t ◇ ((a ◇ a) ◇ ((c ◇ c) ◇ b))) (pv c b c))).trans (p11 a b c b ((b ◇ b) ◇ ((a ◇ a) ◇ ((c ◇ c) ◇ b))) ((b ◇ b) ◇ ((a ◇ a) ◇ ((c ◇ c) ◇ b))))))
  have p22:=fun (a b c d:G)=>by
    exact (p1z a b c d).trans ((p1z a b a d).symm)
  have p23:=fun (a b c d:G)=>by
    exact ((((cg (fun t => ((c ◇ c) ◇ ((c ◇ c) ◇ ((a ◇ a) ◇ (a ◇ (a ◇ c))))) ◇ t) (pb c d ((d ◇ d) ◇ (c ◇ c)))).trans (pi c c ((a ◇ a) ◇ (a ◇ (a ◇ c))) c)).symm).trans (((cg (fun t => t ◇ ((d ◇ d) ◇ (c ◇ c))) (cg (fun t => (c ◇ c) ◇ t) (p22 a a b c))).symm).trans ((h ((b ◇ b) ◇ (a ◇ (a ◇ c))) (c ◇ c) d).symm))).symm
  have p24:=fun (a b c d e:G)=>by
    exact ((p23 b d a ((d ◇ d) ◇ (b ◇ (b ◇ a)))).symm).trans (p1h a b c d e)
  have p25:=fun (a b c:G)=>by
    exact (((cg (fun t => (b ◇ b) ◇ t) (cg (fun t => a ◇ t) (pe c a))).symm).trans (p23 a b (a ◇ (c ◇ c)) c)).trans (cg (fun t => (a ◇ a) ◇ t) (cg (fun t => a ◇ t) (pe c a)))
  have p26:=fun (a b c:G)=>by
    exact ((cg (fun t => (c ◇ c) ◇ t) (cg (fun t => b ◇ t) (cg (fun t => t ◇ b) (p9 a b a)))).symm).trans (p25 b c a)
  have p27:=fun (a b:G)=>by
    exact ((p20 a b a b).trans ((p1c a ((b ◇ b) ◇ b)).symm)).trans (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (cg (fun t => t ◇ ((b ◇ b) ◇ b)) (pv b b b)))
  have p28:=fun (a b c d:G)=>by
    exact (((((cg (fun t => t ◇ ((b ◇ b) ◇ (a ◇ a))) (cg (fun t => (a ◇ a) ◇ t) (p1f c a d))).trans (cg (fun t => t ◇ ((b ◇ b) ◇ (a ◇ a))) (cg (fun t => (a ◇ a) ◇ t) (p1f d a a)))).trans (cg (fun t => ((a ◇ a) ◇ (((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a)) ◇ t) (pb a b ((b ◇ b) ◇ (a ◇ a))))).trans (cg (fun t => t ◇ (a ◇ a)) (p27 a a))).symm).trans (((cg (fun t => t ◇ ((b ◇ b) ◇ (a ◇ a))) (cg (fun t => (a ◇ a) ◇ t) (p19 c a c d c))).symm).trans ((h (a ◇ (a ◇ ((a ◇ a) ◇ a))) (a ◇ a) b).symm))
  have p29:=fun (a b c d:G)=>by
    exact (((((cg (fun t => ((((c ◇ c) ◇ c) ◇ ((c ◇ c) ◇ c)) ◇ (((b ◇ b) ◇ ((a ◇ a) ◇ c)) ◇ c)) ◇ t) (cg (fun t => (d ◇ d) ◇ t) (cg (fun t => ((c ◇ c) ◇ c) ◇ t) (p1v c a b c)))).trans (cg (fun t => t ◇ ((d ◇ d) ◇ (((c ◇ c) ◇ c) ◇ ((c ◇ c) ◇ c)))) (cg (fun t => t ◇ (((b ◇ b) ◇ ((a ◇ a) ◇ c)) ◇ c)) (pv c c c)))).trans (cg (fun t => ((c ◇ c) ◇ (((b ◇ b) ◇ ((a ◇ a) ◇ c)) ◇ c)) ◇ t) (cg (fun t => (d ◇ d) ◇ t) (pv c c c)))).trans (cg (fun t => ((c ◇ c) ◇ (((b ◇ b) ◇ ((a ◇ a) ◇ c)) ◇ c)) ◇ t) (pb c d ((d ◇ d) ◇ (c ◇ c))))).symm).trans ((((cg (fun t => t ◇ ((d ◇ d) ◇ (((c ◇ c) ◇ c) ◇ (((c ◇ c) ◇ c) ◇ (((b ◇ b) ◇ ((a ◇ a) ◇ c)) ◇ c))))) (cg (fun t => t ◇ (((b ◇ b) ◇ ((a ◇ a) ◇ c)) ◇ c)) (cg (fun t => ((c ◇ c) ◇ c) ◇ t) (p1d a b c)))).symm).trans (p13 (((b ◇ b) ◇ ((a ◇ a) ◇ c)) ◇ c) ((c ◇ c) ◇ c) d)).trans (cg (fun t => t ◇ ((c ◇ c) ◇ c)) (pv c c c)))
  have p2a:=fun (a:G)=>by
    exact ((((cg (fun t => t ◇ (a ◇ a)) (p27 a a)).trans (p28 a ((((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ a))) ◇ (a ◇ a)) ((((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ a))) ◇ (a ◇ a)) ((((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ a))) ◇ (a ◇ a)))).symm).trans (((cg (fun t => t ◇ (a ◇ a)) (cg (fun t => (a ◇ a) ◇ t) (cg (fun t => t ◇ a) ((pm a a a).symm)))).symm).trans (p29 a a a a))).symm
  have p2b:=fun (a b:G)=>by
    exact (((po a b).symm).trans (((cg (fun t => t ◇ ((b ◇ b) ◇ b)) (p9 a b a)).symm).trans (p2a b))).symm
  have p2c:=fun (a b c:G)=>by
    exact ((p2a c).symm).trans (pl a b c c)
  have p2d:=fun (a b c:G)=>by
    exact ((p21 a b a c).symm).trans (((cg (fun t => t ◇ ((c ◇ c) ◇ b)) (cg (fun t => b ◇ t) (p2b a b))).symm).trans ((h (b ◇ ((b ◇ b) ◇ b)) b c).symm))
  have p2e:=fun (a b c d:G)=>by
    exact ((p21 b c a d).symm).trans (((cg (fun t => t ◇ ((d ◇ d) ◇ c)) (cg (fun t => c ◇ t) (p2c a b c))).symm).trans ((h (c ◇ ((c ◇ c) ◇ c)) c d).symm))
  have p2f:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (b ◇ b)) (p2d a a a)).symm).trans (p1y a a a b)
  have p2g:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ (c ◇ c)) (cg (fun t => b ◇ t) (cg (fun t => t ◇ b) (p9 a b a)))).symm).trans (p2f b c)
  have p2h:=fun (a b:G)=>by
    exact (((p1e a a b).symm).trans ((((cg (fun t => (a ◇ ((a ◇ a) ◇ a)) ◇ t) (p2f a b)).symm).trans (pe b (a ◇ ((a ◇ a) ◇ a)))).trans (p26 a a (a ◇ ((a ◇ a) ◇ a))))).symm
  have p2i:=fun (a b c:G)=>by
    exact (p26 a b c).trans (p2h b ((b ◇ b) ◇ (b ◇ ((b ◇ b) ◇ b))))
  have p2j:=fun (a b:G)=>by
    exact ((cg (fun t => ((a ◇ a) ◇ b) ◇ t) (p2d a b a)).symm).trans (p1v a a a b)
  have p2k:=fun (a b:G)=>by
    exact ((((((cg (fun t => ((((a ◇ a) ◇ b) ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ ((b ◇ b) ◇ b))) ◇ t) (cg (fun t => ((b ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ ((b ◇ b) ◇ b))) ◇ t) (cg (fun t => ((a ◇ a) ◇ b) ◇ t) (p2j a b)))).trans (cg (fun t => t ◇ (((b ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ ((b ◇ b) ◇ b))) ◇ (((a ◇ a) ◇ b) ◇ ((b ◇ b) ◇ b)))) (cg (fun t => t ◇ (b ◇ ((b ◇ b) ◇ b))) (pv a b b)))).trans (cg (fun t => ((b ◇ b) ◇ (b ◇ ((b ◇ b) ◇ b))) ◇ t) (cg (fun t => ((b ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ ((b ◇ b) ◇ b))) ◇ t) (pv a b b)))).trans (cg (fun t => t ◇ (((b ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ ((b ◇ b) ◇ b))) ◇ (b ◇ b))) (p2i b b b))).trans (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (pb b (b ◇ ((b ◇ b) ◇ b)) (((b ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ ((b ◇ b) ◇ b))) ◇ (b ◇ b))))).symm).trans ((((cg (fun t => t ◇ (((b ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ ((b ◇ b) ◇ b))) ◇ (((a ◇ a) ◇ b) ◇ (((a ◇ a) ◇ b) ◇ (b ◇ ((b ◇ b) ◇ b)))))) (cg (fun t => t ◇ (b ◇ ((b ◇ b) ◇ b))) (cg (fun t => ((a ◇ a) ◇ b) ◇ t) (p2j a b)))).symm).trans (p1o (b ◇ ((b ◇ b) ◇ b)) ((a ◇ a) ◇ b) a a a)).trans ((cg (fun t => t ◇ ((a ◇ a) ◇ b)) (pv a b a)).trans (p10 a b)))
  have p2l:=fun (a b c:G)=>by
    exact ((p1s a c c ((c ◇ (a ◇ a)) ◇ (c ◇ c))).symm).trans (((cg (fun t => t ◇ (c ◇ c)) (cg (fun t => c ◇ t) (p9 a c a))).symm).trans (p2k b c))
  have p2m:=fun (a b c d e f:G)=>by
    exact (p11 a c d e b f).trans (p2e d a c (((a ◇ a) ◇ ((d ◇ d) ◇ c)) ◇ c))
  have p2n:=fun (a b c:G)=>by
    exact ((cg (fun t => ((b ◇ b) ◇ c) ◇ t) (cg (fun t => c ◇ t) (cg (fun t => t ◇ c) (p9 a c a)))).symm).trans (p2j b c)
  have p2o:=fun (a b c d:G)=>by
    exact (((cg (fun t => ((b ◇ (a ◇ a)) ◇ (a ◇ a)) ◇ t) (pb c d ((d ◇ d) ◇ (c ◇ c)))).trans (p1s a (b ◇ (a ◇ a)) c (((b ◇ (a ◇ a)) ◇ (a ◇ a)) ◇ (c ◇ c)))).symm).trans (((cg (fun t => t ◇ ((d ◇ d) ◇ (c ◇ c))) ((p2l a c b).symm)).symm).trans ((h b (c ◇ c) d).symm))
  have p2p:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ ((b ◇ b) ◇ (b ◇ b))) (cg (fun t => a ◇ t) (pb b b ((b ◇ b) ◇ (b ◇ b))))).trans (cg (fun t => (a ◇ (b ◇ b)) ◇ t) (pb b b ((b ◇ b) ◇ (b ◇ b))))).symm).trans (((cg (fun t => t ◇ ((b ◇ b) ◇ (b ◇ b))) (cg (fun t => t ◇ ((b ◇ b) ◇ (b ◇ b))) ((h a (b ◇ b) b).symm))).symm).trans (p2o (b ◇ b) ((b ◇ b) ◇ ((b ◇ b) ◇ a)) a a))
  have p2q:=fun (a b c d:G)=>by
    exact (p1s a b c d).trans (p2p b a)
  have p2r:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (b ◇ b)) ((pr b a a).symm)).symm).trans (p2p a b)).symm
  have p2s:=fun (a b c:G)=>by
    exact ((cg (fun t => (c ◇ c) ◇ t) (cg (fun t => t ◇ b) (p9 a c a))).symm).trans (p2r b c)
  have p2t:=fun (a b c d e f:G)=>by
    exact ((((((cg (fun t => ((((b ◇ (b ◇ a)) ◇ a) ◇ ((c ◇ c) ◇ b)) ◇ ((e ◇ e) ◇ (b ◇ (b ◇ a)))) ◇ t) (cg (fun t => (d ◇ d) ◇ t) (cg (fun t => ((b ◇ (b ◇ a)) ◇ a) ◇ t) (cg (fun t => ((b ◇ (b ◇ a)) ◇ a) ◇ t) (p23 b e a ((e ◇ e) ◇ (b ◇ (b ◇ a)))))))).trans (cg (fun t => ((((b ◇ (b ◇ a)) ◇ a) ◇ ((c ◇ c) ◇ b)) ◇ ((e ◇ e) ◇ (b ◇ (b ◇ a)))) ◇ t) (cg (fun t => (d ◇ d) ◇ t) (cg (fun t => ((b ◇ (b ◇ a)) ◇ a) ◇ t) (cg (fun t => ((b ◇ (b ◇ a)) ◇ a) ◇ t) (p24 a b ((b ◇ b) ◇ (b ◇ (b ◇ a))) ((b ◇ b) ◇ (b ◇ (b ◇ a))) ((b ◇ b) ◇ (b ◇ (b ◇ a))))))))).trans (cg (fun t => ((((b ◇ (b ◇ a)) ◇ a) ◇ ((c ◇ c) ◇ b)) ◇ ((e ◇ e) ◇ (b ◇ (b ◇ a)))) ◇ t) (cg (fun t => (d ◇ d) ◇ t) (cg (fun t => ((b ◇ (b ◇ a)) ◇ a) ◇ t) (p1o a b (((b ◇ (b ◇ a)) ◇ a) ◇ ((a ◇ a) ◇ (b ◇ (b ◇ a)))) (((b ◇ (b ◇ a)) ◇ a) ◇ ((a ◇ a) ◇ (b ◇ (b ◇ a)))) (((b ◇ (b ◇ a)) ◇ a) ◇ ((a ◇ a) ◇ (b ◇ (b ◇ a))))))))).trans (cg (fun t => t ◇ ((d ◇ d) ◇ (((b ◇ (b ◇ a)) ◇ a) ◇ ((b ◇ b) ◇ b)))) (cg (fun t => (((b ◇ (b ◇ a)) ◇ a) ◇ ((c ◇ c) ◇ b)) ◇ t) (p23 b e a ((e ◇ e) ◇ (b ◇ (b ◇ a))))))).trans (cg (fun t => t ◇ ((d ◇ d) ◇ (((b ◇ (b ◇ a)) ◇ a) ◇ ((b ◇ b) ◇ b)))) (cg (fun t => (((b ◇ (b ◇ a)) ◇ a) ◇ ((c ◇ c) ◇ b)) ◇ t) (p24 a b ((b ◇ b) ◇ (b ◇ (b ◇ a))) ((b ◇ b) ◇ (b ◇ (b ◇ a))) ((b ◇ b) ◇ (b ◇ (b ◇ a))))))).symm).trans ((((cg (fun t => t ◇ ((d ◇ d) ◇ (((b ◇ (b ◇ a)) ◇ a) ◇ (((b ◇ (b ◇ a)) ◇ a) ◇ ((e ◇ e) ◇ (b ◇ (b ◇ a))))))) (cg (fun t => t ◇ ((e ◇ e) ◇ (b ◇ (b ◇ a)))) (cg (fun t => ((b ◇ (b ◇ a)) ◇ a) ◇ t) (p0 a b c e)))).symm).trans (p0 ((e ◇ e) ◇ (b ◇ (b ◇ a))) ((b ◇ (b ◇ a)) ◇ a) f d)).trans (p1l a b f))
  have p2u:=fun (a b c d e:G)=>by
    exact (((((((((((cg (fun t => (((((c ◇ c) ◇ ((d ◇ d) ◇ a)) ◇ a) ◇ ((e ◇ e) ◇ (d ◇ d))) ◇ ((a ◇ a) ◇ ((d ◇ d) ◇ ((d ◇ d) ◇ a)))) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (cg (fun t => (((d ◇ d) ◇ ((d ◇ d) ◇ a)) ◇ a) ◇ t) (cg (fun t => t ◇ (d ◇ d)) (pb d d ((d ◇ d) ◇ (d ◇ d))))))).trans (cg (fun t => (((((c ◇ c) ◇ ((d ◇ d) ◇ a)) ◇ a) ◇ ((e ◇ e) ◇ (d ◇ d))) ◇ ((a ◇ a) ◇ ((d ◇ d) ◇ ((d ◇ d) ◇ a)))) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (cg (fun t => (((d ◇ d) ◇ ((d ◇ d) ◇ a)) ◇ a) ◇ t) (pb d d ((d ◇ d) ◇ (d ◇ d))))))).trans (cg (fun t => t ◇ ((b ◇ b) ◇ ((((d ◇ d) ◇ ((d ◇ d) ◇ a)) ◇ a) ◇ (d ◇ d)))) (cg (fun t => t ◇ ((a ◇ a) ◇ ((d ◇ d) ◇ ((d ◇ d) ◇ a)))) (cg (fun t => (((c ◇ c) ◇ ((d ◇ d) ◇ a)) ◇ a) ◇ t) (pb d e ((e ◇ e) ◇ (d ◇ d))))))).trans (cg (fun t => t ◇ ((b ◇ b) ◇ ((((d ◇ d) ◇ ((d ◇ d) ◇ a)) ◇ a) ◇ (d ◇ d)))) (cg (fun t => t ◇ ((a ◇ a) ◇ ((d ◇ d) ◇ ((d ◇ d) ◇ a)))) (cg (fun t => t ◇ (d ◇ d)) (p2e d c a (((c ◇ c) ◇ ((d ◇ d) ◇ a)) ◇ a)))))).trans (cg (fun t => (((a ◇ ((a ◇ a) ◇ a)) ◇ (d ◇ d)) ◇ ((a ◇ a) ◇ ((d ◇ d) ◇ ((d ◇ d) ◇ a)))) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (cg (fun t => t ◇ (d ◇ d)) (p2e d d a (((d ◇ d) ◇ ((d ◇ d) ◇ a)) ◇ a)))))).trans (cg (fun t => t ◇ ((b ◇ b) ◇ ((a ◇ ((a ◇ a) ◇ a)) ◇ (d ◇ d)))) (cg (fun t => t ◇ ((a ◇ a) ◇ ((d ◇ d) ◇ ((d ◇ d) ◇ a)))) (p2g a a d)))).trans (cg (fun t => (((d ◇ d) ◇ a) ◇ ((a ◇ a) ◇ ((d ◇ d) ◇ ((d ◇ d) ◇ a)))) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (p2g a a d)))).trans (cg (fun t => t ◇ ((b ◇ b) ◇ ((d ◇ d) ◇ a))) (cg (fun t => ((d ◇ d) ◇ a) ◇ t) (p2m d ((a ◇ a) ◇ ((d ◇ d) ◇ ((d ◇ d) ◇ a))) a d a ((a ◇ a) ◇ ((d ◇ d) ◇ ((d ◇ d) ◇ a))))))).trans (cg (fun t => (((d ◇ d) ◇ a) ◇ (a ◇ ((a ◇ a) ◇ a))) ◇ t) (p2s d a b))).trans (cg (fun t => t ◇ ((a ◇ (a ◇ a)) ◇ (b ◇ b))) (p2n a d a))).symm).trans ((((cg (fun t => t ◇ ((b ◇ b) ◇ ((((d ◇ d) ◇ ((d ◇ d) ◇ a)) ◇ a) ◇ (((d ◇ d) ◇ (d ◇ d)) ◇ (d ◇ d))))) (cg (fun t => t ◇ ((a ◇ a) ◇ ((d ◇ d) ◇ ((d ◇ d) ◇ a)))) (cg (fun t => t ◇ ((e ◇ e) ◇ (d ◇ d))) (cg (fun t => t ◇ a) (p1 c ((d ◇ d) ◇ a) d c))))).symm).trans (p2t a (d ◇ d) e b c c)).trans ((cg (fun t => (a ◇ a) ◇ t) (p2e d d a (((d ◇ d) ◇ ((d ◇ d) ◇ a)) ◇ a))).trans (p2i a a a)))
  have p2v:=fun (a b c d:G)=>by
    exact ((((cg (fun t => t ◇ (a ◇ (b ◇ b))) (cg (fun t => t ◇ ((c ◇ c) ◇ ((d ◇ d) ◇ a))) (pv c ((d ◇ d) ◇ a) c))).trans (cg (fun t => t ◇ (a ◇ (b ◇ b))) (cg (fun t => t ◇ ((c ◇ c) ◇ ((d ◇ d) ◇ a))) (pv d a d)))).trans (cg (fun t => t ◇ (a ◇ (b ◇ b))) (p2m c ((a ◇ a) ◇ ((c ◇ c) ◇ ((d ◇ d) ◇ a))) a d a ((a ◇ a) ◇ ((c ◇ c) ◇ ((d ◇ d) ◇ a)))))).symm).trans ((((cg (fun t => ((((c ◇ c) ◇ ((d ◇ d) ◇ a)) ◇ ((c ◇ c) ◇ ((d ◇ d) ◇ a))) ◇ ((c ◇ c) ◇ ((d ◇ d) ◇ a))) ◇ t) (cg (fun t => t ◇ (b ◇ b)) (pi c ((c ◇ c) ◇ ((d ◇ d) ◇ a)) a d))).symm).trans (p2u ((c ◇ c) ◇ ((d ◇ d) ◇ a)) b c c c)).trans (((cg (fun t => ((c ◇ c) ◇ ((d ◇ d) ◇ a)) ◇ t) (pv c ((d ◇ d) ◇ a) c)).trans (cg (fun t => ((c ◇ c) ◇ ((d ◇ d) ◇ a)) ◇ t) (pv d a d))).trans (pi c a a d)))
  have p2w:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ ((b ◇ (b ◇ b)) ◇ (c ◇ c))) (cg (fun t => t ◇ b) (p9 a b a))).symm).trans (p2u b c a a a)
  have p2x:=fun (a b c d:G)=>by
    exact ((cg (fun t => ((b ◇ b) ◇ c) ◇ t) (p2q a c d ((c ◇ (a ◇ a)) ◇ (d ◇ d)))).symm).trans (((cg (fun t => ((b ◇ b) ◇ c) ◇ t) (cg (fun t => t ◇ (d ◇ d)) (cg (fun t => c ◇ t) (p9 a c a)))).symm).trans (p2w b c d))
  have p2y:=fun (a b c:G)=>by
    exact ((cg (fun t => ((a ◇ ((a ◇ a) ◇ a)) ◇ a) ◇ t) (p2i a a c)).symm).trans (((cg (fun t => t ◇ ((c ◇ c) ◇ (a ◇ ((a ◇ a) ◇ a)))) (cg (fun t => (a ◇ ((a ◇ a) ◇ a)) ◇ t) (p2v a b a a))).symm).trans ((h (a ◇ (b ◇ b)) (a ◇ ((a ◇ a) ◇ a)) c).symm))
  have p2z:=fun (a b c:G)=>by
    exact (((((cg (fun t => ((((a ◇ a) ◇ b) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ b))) ◇ ((a ◇ a) ◇ b)) ◇ t) (cg (fun t => ((a ◇ a) ◇ b) ◇ t) (pv a b a))).trans (cg (fun t => t ◇ (((a ◇ a) ◇ b) ◇ (b ◇ b))) (cg (fun t => t ◇ ((a ◇ a) ◇ b)) (p2x a a b (((a ◇ a) ◇ b) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ b))))))).trans (cg (fun t => ((b ◇ (b ◇ b)) ◇ ((a ◇ a) ◇ b)) ◇ t) (pz a b))).trans (cg (fun t => t ◇ (((a ◇ a) ◇ b) ◇ (a ◇ a))) (pc b b a))).symm).trans (((cg (fun t => t ◇ (((a ◇ a) ◇ b) ◇ (((a ◇ a) ◇ b) ◇ ((a ◇ a) ◇ b)))) (cg (fun t => t ◇ ((a ◇ a) ◇ b)) (cg (fun t => ((a ◇ a) ◇ b) ◇ t) ((pj ((a ◇ a) ◇ b) a b a).symm)))).symm).trans (p2y ((a ◇ a) ◇ b) c a))
  have p30:=fun (a b:G)=>by
    exact ((cg (fun t => ((a ◇ a) ◇ b) ◇ t) (pi a a b a)).symm).trans ((p2z a ((a ◇ a) ◇ b) (a ◇ a)).trans ((h b (a ◇ a) a).symm))
  exact (calc
    (x ◇ x)=(x ◇ x):=rfl
    _=((((y ◇ y) ◇ x) ◇ x) ◇ x):=(cg (fun t => t ◇ x) (p30 y x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_22618_to_53019 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_22618_to_53019
