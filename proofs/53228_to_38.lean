-- Equation53228 → Equation38
-- Recorded verdict: true
-- Premise: x ◇ y = (((x ◇ z) ◇ y) ◇ y) ◇ x
-- Conclusion: x ◇ x = x ◇ y
-- Original submission SHA-256: ca27b290d11ce606b674646d2d7f899e365d33be2f6323c0dd8c5077a9b3ee6b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (((x ◇ z) ◇ y) ◇ y) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ x = x ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have cg : ∀ (f:G → G) {a b:G}, a=b → f a=f b:=by
    intro f a b p
    exact congrArg f p
  have p0:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (b ◇ a)) ((h b b a).symm)).symm).trans ((h (b ◇ a) b b).symm)
  have p1:=fun (a b c:G)=>by
    exact ((h a b c).symm).trans (h a b a)
  have p2:=fun (a b c:G)=>by
    exact ((h a b a).trans (p1 a b a)).symm
  have p3:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ ((b ◇ a) ◇ c)) (cg (fun t => t ◇ b) ((h b c a).symm))).symm).trans ((h ((b ◇ a) ◇ c) b c).symm)
  have p4:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ b) (cg (fun t => t ◇ (b ◇ a)) (p0 a b))).symm).trans ((h b (b ◇ a) b).symm)
  have p5:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ ((a ◇ a) ◇ b)) (p0 a a)).symm).trans (p0 b (a ◇ a))
  have p6:=fun (a b:G)=>by
    exact (((p3 a b b).symm).trans ((((cg (fun t => ((b ◇ b) ◇ b) ◇ t) (p0 a b)).symm).trans (p5 b (b ◇ a))).trans (cg (fun t => t ◇ (b ◇ b)) (p0 a b)))).symm
  have p7:=fun (a:G)=>by
    exact (((p2 a a ((((a ◇ a) ◇ a) ◇ a) ◇ a)).symm).trans (((cg (fun t => t ◇ a) (p6 a a)).symm).trans (p4 a a))).symm
  have p8:=fun (a:G)=>by
    exact ((((((cg (fun t => t ◇ a) (cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) (p0 a a))).trans (cg (fun t => t ◇ a) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (p0 a a)))).trans (cg (fun t => t ◇ a) (p3 a a a))).trans (p2 a a ((((a ◇ a) ◇ a) ◇ a) ◇ a))).symm).trans ((((cg (fun t => t ◇ a) (cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) (p7 (a ◇ a)))).symm).trans (p2 a ((a ◇ a) ◇ (a ◇ a)) a)).trans (cg (fun t => a ◇ t) (p0 a a)))).symm
  have p9:=fun (a:G)=>by
    exact (((cg (fun t => (a ◇ a) ◇ t) (p0 a a)).symm).trans (p7 (a ◇ a))).trans (p0 a a)
  have pa:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ (b ◇ b)) (cg (fun t => t ◇ c) (cg (fun t => t ◇ c) (p0 a b)))).symm).trans ((h (b ◇ b) c (b ◇ a)).symm)
  have pb:=fun (a b:G)=>by
    exact (((cg (fun t => ((b ◇ (b ◇ a)) ◇ b) ◇ t) (p0 a b)).symm).trans (p3 b b (b ◇ a))).trans (cg (fun t => t ◇ b) (p0 a b))
  have pc:=fun (a:G)=>by
    exact (((cg (fun t => ((a ◇ a) ◇ a) ◇ t) (p3 a a a)).symm).trans (p7 ((a ◇ a) ◇ a))).trans (p3 a a a)
  have pd:=fun (a b c d:G)=>by
    exact ((cg (fun t => t ◇ (((d ◇ b) ◇ a) ◇ a)) (cg (fun t => t ◇ c) (cg (fun t => t ◇ c) ((h d a b).symm)))).symm).trans ((h (((d ◇ b) ◇ a) ◇ a) c d).symm)
  have pe:=fun (a b c:G)=>by
    exact (((pa a b c).symm).trans (((cg (fun t => ((((b ◇ a) ◇ b) ◇ c) ◇ c) ◇ t) ((h b b a).symm)).symm).trans (pd b b c (b ◇ a)))).symm
  have pf:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ ((((c ◇ a) ◇ b) ◇ c) ◇ c)) ((h c c a).symm)).symm).trans (pd c b c (c ◇ a))).symm
  have pg:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ ((((b ◇ b) ◇ a) ◇ b) ◇ b)) (p2 b b a)).symm).trans (pd b a b (b ◇ b))).symm
  have ph:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ a) (p0 (a ◇ b) (a ◇ b))).symm).trans (((cg (fun t => t ◇ a) (cg (fun t => t ◇ ((a ◇ b) ◇ (a ◇ b))) (p7 (a ◇ b)))).symm).trans ((h a ((a ◇ b) ◇ (a ◇ b)) b).symm))
  have pi:=fun (a b:G)=>by
    exact ((ph a b).symm).trans ((h a (a ◇ b) b).symm)
  have pj:=fun (a b:G)=>by
    exact (ph a b).trans (pi a b)
  have pk:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (b ◇ b)) (cg (fun t => t ◇ (b ◇ b)) (p6 a b))).symm).trans (pa a b (b ◇ b))).trans (p0 b b)
  have pl:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ (((b ◇ a) ◇ b) ◇ b)) (p6 b b)).trans (pd b a b b)).symm).trans (((cg (fun t => t ◇ (((b ◇ a) ◇ b) ◇ b)) (cg (fun t => t ◇ (b ◇ b)) (pk a b))).symm).trans ((h (((b ◇ a) ◇ b) ◇ b) (b ◇ b) (b ◇ b)).symm))).symm
  have pm:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ (((a ◇ b) ◇ a) ◇ a)) (p3 a a a)).trans (pd a b a a)).symm).trans (((cg (fun t => t ◇ (((a ◇ b) ◇ a) ◇ a)) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (p9 a))).symm).trans (pd a b ((a ◇ a) ◇ a) a))).symm
  have pn:=fun (a b:G)=>by
    exact (((((cg (fun t => t ◇ ((b ◇ a) ◇ b)) (pe a b ((b ◇ b) ◇ b))).trans (cg (fun t => t ◇ ((b ◇ a) ◇ b)) (p9 b))).trans (p3 a b b)).symm).trans (((cg (fun t => t ◇ ((b ◇ a) ◇ b)) (cg (fun t => t ◇ ((b ◇ b) ◇ b)) (pm b a))).symm).trans ((h ((b ◇ a) ◇ b) ((b ◇ b) ◇ b) b).symm))).symm
  have po:=fun (a b:G)=>by
    exact (((((cg (fun t => t ◇ (b ◇ a)) (pm b a)).trans (pe a b (b ◇ a))).trans (p0 a b)).symm).trans (((cg (fun t => t ◇ (b ◇ a)) (cg (fun t => t ◇ ((b ◇ b) ◇ b)) (pn a b))).symm).trans ((h (b ◇ a) ((b ◇ b) ◇ b) b).symm))).symm
  have pp:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ a) (pn b a)).symm).trans ((((cg (fun t => t ◇ a) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (po b a))).symm).trans ((h a ((a ◇ a) ◇ a) b).symm)).trans (p8 a))
  have pq:=fun (a b:G)=>by
    exact (pl a b).trans (pp b a)
  have pr:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ (b ◇ a)) (pq a b)).trans (p0 a b)).symm).trans (((cg (fun t => t ◇ (b ◇ a)) (cg (fun t => t ◇ (b ◇ b)) (p6 a b))).symm).trans ((h (b ◇ a) (b ◇ b) b).symm))).symm
  have ps:=fun (a b:G)=>by
    exact (((((cg (fun t => t ◇ (b ◇ b)) (p6 b (b ◇ a))).trans (pa a b (b ◇ a))).trans (p0 a b)).symm).trans (((cg (fun t => t ◇ (b ◇ b)) (cg (fun t => t ◇ ((b ◇ a) ◇ (b ◇ a))) (pr b (b ◇ a)))).symm).trans (pa a b ((b ◇ a) ◇ (b ◇ a))))).symm
  have pt:=fun (a b c:G)=>by
    exact ((((cg (fun t => t ◇ (((c ◇ b) ◇ a) ◇ a)) (p6 a c)).trans (pd a b c c)).symm).trans (((cg (fun t => t ◇ (((c ◇ b) ◇ a) ◇ a)) (cg (fun t => t ◇ (c ◇ c)) (pr a c))).symm).trans (pd a b (c ◇ c) c))).symm
  have pu:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (b ◇ b)) (cg (fun t => t ◇ (b ◇ a)) (p0 a b))).symm).trans (pt (b ◇ a) b b)).trans ((cg (fun t => t ◇ b) (cg (fun t => t ◇ (b ◇ a)) (p0 a b))).trans (p4 a b))
  have pv:=fun (a b c:G)=>by
    exact ((cg (fun t => ((((c ◇ b) ◇ a) ◇ a) ◇ (((c ◇ b) ◇ a) ◇ a)) ◇ t) ((h c a b).symm)).symm).trans (p0 c (((c ◇ b) ◇ a) ◇ a))
  have pw:=fun (a b:G)=>by
    exact (pm a b).trans (pp a b)
  have px:=fun (a b c:G)=>by
    exact ((cg (fun t => ((((b ◇ a) ◇ b) ◇ c) ◇ c) ◇ t) (p0 b b)).symm).trans ((((cg (fun t => t ◇ ((b ◇ b) ◇ (b ◇ b))) (cg (fun t => t ◇ c) (cg (fun t => t ◇ c) (p0 a b)))).symm).trans (pt c (b ◇ a) (b ◇ b))).trans ((cg (fun t => t ◇ (b ◇ b)) (cg (fun t => t ◇ c) (cg (fun t => t ◇ c) (p0 a b)))).trans (pa a b c)))
  have py:=fun (a b:G)=>by
    exact (((((((cg (fun t => t ◇ ((((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ a))) (cg (fun t => t ◇ b) (cg (fun t => t ◇ b) (pw a a)))).trans (cg (fun t => (((a ◇ a) ◇ b) ◇ b) ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (p3 a a a)))).trans (cg (fun t => (((a ◇ a) ◇ b) ◇ b) ◇ t) (pw a a))).trans (pt b a a)).trans (p2 a b ((((a ◇ a) ◇ b) ◇ b) ◇ a))).symm).trans ((((cg (fun t => t ◇ ((((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ a))) (cg (fun t => t ◇ b) (cg (fun t => t ◇ b) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (pc a))))).symm).trans (px (((a ◇ a) ◇ a) ◇ a) ((a ◇ a) ◇ a) b)).trans (cg (fun t => t ◇ b) (p3 a a a)))).symm
  have pz:=fun (a b:G)=>by
    exact (((py b (((b ◇ a) ◇ b) ◇ b)).symm).trans (pd b a b b)).trans (pp b a)
  have p10:=fun (a b:G)=>by
    exact (((((cg (fun t => (a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ t) (py a b)).trans (cg (fun t => t ◇ (a ◇ b)) (pz a a))).trans (p0 b a)).symm).trans ((((cg (fun t => t ◇ ((((a ◇ a) ◇ a) ◇ a) ◇ b)) (py a (((a ◇ a) ◇ a) ◇ a))).symm).trans (p0 b (((a ◇ a) ◇ a) ◇ a))).trans (cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ a)) (py a b)))).symm
  have p11:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ ((b ◇ b) ◇ b)) (cg (fun t => t ◇ a) (py b a))).symm).trans ((h ((b ◇ b) ◇ b) a b).symm)
  have p12:=fun (a b c d:G)=>by
    exact ((cg (fun t => t ◇ ((b ◇ c) ◇ b)) (cg (fun t => t ◇ d) (cg (fun t => t ◇ d) (p3 a b c)))).symm).trans ((h ((b ◇ c) ◇ b) d ((b ◇ a) ◇ c)).symm)
  have p13:=fun (a b:G)=>by
    exact (((py a (((a ◇ a) ◇ b) ◇ a)).symm).trans (((cg (fun t => t ◇ (((a ◇ a) ◇ b) ◇ a)) (p6 a a)).symm).trans (p3 b (a ◇ a) a))).symm
  have p14:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ ((((a ◇ a) ◇ b) ◇ a) ◇ a)) (p7 a)).symm).trans (((cg (fun t => t ◇ ((((a ◇ a) ◇ b) ◇ a) ◇ a)) (pu a a)).symm).trans (pd a b (a ◇ a) (a ◇ a)))).symm
  have p15:=fun (a b:G)=>by
    exact ((p14 a b).symm).trans ((h (a ◇ a) a b).symm)
  have p16:=fun (a b:G)=>by
    exact (pg a b).trans (p15 b a)
  have p17:=fun (a b:G)=>by
    exact ((p5 b a).symm).trans (((cg (fun t => t ◇ ((b ◇ b) ◇ a)) (p16 a b)).symm).trans ((h ((b ◇ b) ◇ a) b b).symm))
  have p18:=fun (a b:G)=>by
    exact (((py b (((b ◇ b) ◇ a) ◇ b)).symm).trans (((cg (fun t => t ◇ (((b ◇ b) ◇ a) ◇ b)) (cg (fun t => t ◇ b) (p16 a b))).symm).trans ((h (((b ◇ b) ◇ a) ◇ b) b b).symm))).symm
  have p19:=fun (a b:G)=>by
    exact ((((((cg (fun t => t ◇ ((((b ◇ b) ◇ a) ◇ b) ◇ b)) (cg (fun t => (((b ◇ b) ◇ b) ◇ b) ◇ t) (cg (fun t => t ◇ b) (p16 a b)))).trans (cg (fun t => t ◇ ((((b ◇ b) ◇ a) ◇ b) ◇ b)) (pd b b b b))).trans (cg (fun t => t ◇ ((((b ◇ b) ◇ a) ◇ b) ◇ b)) (p2 b b ((((b ◇ b) ◇ b) ◇ b) ◇ b)))).trans (p15 b a)).symm).trans ((((cg (fun t => t ◇ ((((b ◇ b) ◇ a) ◇ b) ◇ b)) (cg (fun t => t ◇ ((((((b ◇ b) ◇ a) ◇ b) ◇ b) ◇ b) ◇ b)) (cg (fun t => t ◇ b) (p16 a b)))).symm).trans (pv b b (((b ◇ b) ◇ a) ◇ b))).trans ((((cg (fun t => t ◇ ((((((b ◇ b) ◇ a) ◇ b) ◇ b) ◇ b) ◇ b)) (cg (fun t => t ◇ (((b ◇ b) ◇ a) ◇ b)) (cg (fun t => t ◇ b) (p16 a b)))).trans (cg (fun t => ((((b ◇ b) ◇ b) ◇ b) ◇ (((b ◇ b) ◇ a) ◇ b)) ◇ t) (cg (fun t => t ◇ b) (p16 a b)))).trans (cg (fun t => t ◇ (((b ◇ b) ◇ b) ◇ b)) (py b (((b ◇ b) ◇ a) ◇ b)))).trans (p10 b (((b ◇ b) ◇ a) ◇ b))))).symm
  have p1a:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ a)) (cg (fun t => t ◇ b) (cg (fun t => t ◇ b) (py a c)))).symm).trans ((h (((a ◇ a) ◇ a) ◇ a) b c).symm)).trans (py a b)
  have p1b:=fun (a b c:G)=>by
    exact ((((cg (fun t => ((((a ◇ a) ◇ c) ◇ b) ◇ b) ◇ t) (cg (fun t => t ◇ (a ◇ a)) (p6 a a))).trans (cg (fun t => ((((a ◇ a) ◇ c) ◇ b) ◇ b) ◇ t) (pt a a a))).trans (cg (fun t => ((((a ◇ a) ◇ c) ◇ b) ◇ b) ◇ t) (p2 a a ((((a ◇ a) ◇ a) ◇ a) ◇ a)))).symm).trans (((cg (fun t => ((((a ◇ a) ◇ c) ◇ b) ◇ b) ◇ t) (cg (fun t => t ◇ (a ◇ a)) (cg (fun t => t ◇ (a ◇ a)) (p0 a a)))).symm).trans (p1a (a ◇ a) b c))
  have p1c:=fun (a b c:G)=>by
    exact ((((cg (fun t => t ◇ ((a ◇ b) ◇ c)) (p10 a c)).trans (p3 b a c)).symm).trans (((cg (fun t => t ◇ ((a ◇ b) ◇ c)) (cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ a)) (p1a a c b))).symm).trans ((h ((a ◇ b) ◇ c) (((a ◇ a) ◇ a) ◇ a) c).symm))).symm
  have p1d:=fun (a b c:G)=>by
    exact ((((cg (fun t => t ◇ (((c ◇ b) ◇ a) ◇ a)) (pn a c)).trans (pd a b c c)).symm).trans (((cg (fun t => t ◇ (((c ◇ b) ◇ a) ◇ a)) (cg (fun t => t ◇ ((c ◇ c) ◇ c)) (po a c))).symm).trans (pd a b ((c ◇ c) ◇ c) c))).symm
  have p1e:=fun (a b:G)=>by
    exact ((((cg (fun t => ((b ◇ a) ◇ a) ◇ t) (cg (fun t => t ◇ ((b ◇ b) ◇ b)) (p3 b b b))).trans (cg (fun t => ((b ◇ a) ◇ a) ◇ t) (py b ((b ◇ b) ◇ b)))).trans (cg (fun t => ((b ◇ a) ◇ a) ◇ t) (p8 b))).symm).trans ((((cg (fun t => t ◇ ((((b ◇ b) ◇ b) ◇ ((b ◇ b) ◇ b)) ◇ ((b ◇ b) ◇ b))) (cg (fun t => t ◇ a) (py b a))).symm).trans (p1d a b ((b ◇ b) ◇ b))).trans ((cg (fun t => t ◇ ((b ◇ b) ◇ b)) (cg (fun t => t ◇ a) (py b a))).trans (p11 a b)))
  have p1f:=fun (a b c:G)=>by
    exact ((((cg (fun t => t ◇ (((c ◇ b) ◇ a) ◇ a)) (p0 (c ◇ a) (c ◇ a))).trans (pd a b (c ◇ a) c)).symm).trans (((cg (fun t => t ◇ (((c ◇ b) ◇ a) ◇ a)) (cg (fun t => t ◇ ((c ◇ a) ◇ (c ◇ a))) (p7 (c ◇ a)))).symm).trans (pd a b ((c ◇ a) ◇ (c ◇ a)) c))).symm
  have p1g:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ (((b ◇ c) ◇ b) ◇ b)) (cg (fun t => t ◇ (b ◇ a)) (p0 a b))).symm).trans (pd b c (b ◇ a) b)
  have p1h:=fun (a b c d:G)=>by
    exact (((cg (fun t => t ◇ (((((d ◇ a) ◇ b) ◇ c) ◇ b) ◇ b)) (cg (fun t => t ◇ d) ((h d b a).symm))).symm).trans (pd b c d ((d ◇ a) ◇ b))).symm
  have p1i:=fun (a b:G)=>by
    exact (((pt a a b).symm).trans ((((cg (fun t => t ◇ (b ◇ b)) (cg (fun t => t ◇ a) (cg (fun t => t ◇ a) (p2 b a a)))).symm).trans (p1h a a b (b ◇ b))).trans ((cg (fun t => (((b ◇ b) ◇ a) ◇ (b ◇ b)) ◇ t) (cg (fun t => t ◇ a) (cg (fun t => t ◇ a) (p2 b a ((((b ◇ b) ◇ a) ◇ a) ◇ b))))).trans (cg (fun t => t ◇ (((b ◇ a) ◇ a) ◇ a)) (p17 a b))))).symm
  have p1j:=fun (a b:G)=>by
    exact (((((cg (fun t => (((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ b) ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ t) (cg (fun t => t ◇ b) (cg (fun t => t ◇ b) (py a b)))).trans (cg (fun t => t ◇ (((a ◇ b) ◇ b) ◇ b)) (cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ a)) (cg (fun t => t ◇ b) (pz a a))))).trans (cg (fun t => t ◇ (((a ◇ b) ◇ b) ◇ b)) (p1c a a b))).trans (p1i b a)).symm).trans ((((cg (fun t => t ◇ ((((((a ◇ a) ◇ a) ◇ a) ◇ b) ◇ b) ◇ b)) (cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ a)) (cg (fun t => t ◇ b) (py a (((a ◇ a) ◇ a) ◇ a))))).symm).trans (p1i b (((a ◇ a) ◇ a) ◇ a))).trans ((cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ a)) (cg (fun t => t ◇ b) (cg (fun t => t ◇ b) (py a b)))).trans (p1a a b b)))
  have p1k:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ (b ◇ a)) (pd a a a b)).trans (p1j (b ◇ a) a)).symm).trans ((((cg (fun t => ((((b ◇ a) ◇ a) ◇ a) ◇ (((b ◇ a) ◇ a) ◇ a)) ◇ t) (p1j b a)).symm).trans (p0 b (((b ◇ a) ◇ a) ◇ a))).trans (cg (fun t => t ◇ (((b ◇ a) ◇ a) ◇ a)) (p1j b a)))).symm
  have p1l:=fun (a b:G)=>by
    exact (p1i a b).trans (p1j b a)
  have p1m:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ a) ◇ t) (pd a a a b)).symm).trans ((((cg (fun t => t ◇ ((((b ◇ a) ◇ a) ◇ a) ◇ (((b ◇ a) ◇ a) ◇ a))) (p1j b a)).symm).trans (pr b (((b ◇ a) ◇ a) ◇ a))).trans ((cg (fun t => t ◇ (((b ◇ a) ◇ a) ◇ a)) (p1j b a)).trans (p1k a b)))
  have p1n:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ a) (p1k b (a ◇ b))).trans (p1j a b)).symm).trans (((cg (fun t => t ◇ a) (cg (fun t => t ◇ ((((a ◇ b) ◇ b) ◇ b) ◇ b)) (p1m b a))).symm).trans ((h a ((((a ◇ b) ◇ b) ◇ b) ◇ b) b).symm))).symm
  have p1o:=fun (a b c:G)=>by
    exact ((((cg (fun t => t ◇ (((b ◇ b) ◇ b) ◇ b)) (p1m a (b ◇ c))).trans (p1a b a c)).symm).trans (((cg (fun t => t ◇ (((b ◇ b) ◇ b) ◇ b)) (cg (fun t => t ◇ (((((b ◇ c) ◇ a) ◇ a) ◇ a) ◇ a)) (p1n (b ◇ c) a))).symm).trans (p1a b (((((b ◇ c) ◇ a) ◇ a) ◇ a) ◇ a) c))).symm
  have p1p:=fun (a b c:G)=>by
    exact ((cg (fun t => ((b ◇ a) ◇ c) ◇ t) (pp b c)).symm).trans (((cg (fun t => ((b ◇ a) ◇ c) ◇ t) (cg (fun t => t ◇ b) (cg (fun t => t ◇ b) (cg (fun t => t ◇ b) ((h b c a).symm))))).symm).trans (p1o b ((b ◇ a) ◇ c) c))
  have p1q:=fun (a b c d:G)=>by
    exact (((p12 a b c d).symm).trans (((cg (fun t => (((((b ◇ a) ◇ c) ◇ b) ◇ d) ◇ d) ◇ t) (cg (fun t => t ◇ b) ((h b c a).symm))).symm).trans (pd b c d ((b ◇ a) ◇ c)))).symm
  have p1r:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ ((((c ◇ a) ◇ b) ◇ b) ◇ c)) (pp c b)).symm).trans (((cg (fun t => t ◇ ((((c ◇ a) ◇ b) ◇ b) ◇ c)) (cg (fun t => t ◇ c) (p1q a c b c))).symm).trans (p1j ((((c ◇ a) ◇ b) ◇ b) ◇ c) c))).symm
  have p1s:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ c) ((h c b a).symm)).symm).trans (p1r a b c)).symm
  have p1t:=fun (a b c:G)=>by
    exact (p1r a b c).trans (p1s a b c)
  have p1u:=fun (a b:G)=>by
    exact (((cg (fun t => (((b ◇ a) ◇ a) ◇ a) ◇ t) (pd a a a b)).symm).trans (p7 (((b ◇ a) ◇ a) ◇ a))).trans (pd a a a b)
  have p1v:=fun (a b:G)=>by
    exact (((p1f a a b).symm).trans (p1e a (b ◇ a))).symm
  have p1w:=fun (a b:G)=>by
    exact (((p1k b (a ◇ b)).symm).trans (((cg (fun t => ((a ◇ b) ◇ b) ◇ t) (pd b b b a)).symm).trans (pi ((a ◇ b) ◇ b) b))).symm
  have p1x:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ ((c ◇ a) ◇ b)) (pf a b c)).symm).trans ((h ((c ◇ a) ◇ b) c c).symm)
  have p1y:=fun (a b c:G)=>by
    exact ((cg (fun t => (((c ◇ a) ◇ b) ◇ c) ◇ t) (p16 ((((c ◇ a) ◇ b) ◇ c) ◇ c) c)).symm).trans (((cg (fun t => (((c ◇ a) ◇ b) ◇ c) ◇ t) (cg (fun t => t ◇ c) (cg (fun t => t ◇ c) (cg (fun t => t ◇ c) (pf a b c))))).symm).trans (p1o c (((c ◇ a) ◇ b) ◇ c) c))
  have p1z:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (((a ◇ a) ◇ b) ◇ ((a ◇ a) ◇ b))) (p0 a a)).symm).trans (ps b (a ◇ a))).trans (p1p a a b)
  have p20:=fun (a b c:G)=>by
    exact (((((cg (fun t => (((a ◇ a) ◇ b) ◇ c) ◇ t) (cg (fun t => t ◇ (a ◇ a)) (cg (fun t => t ◇ (a ◇ a)) (p1p a a c)))).trans (cg (fun t => (((a ◇ a) ◇ b) ◇ c) ◇ t) (cg (fun t => t ◇ (a ◇ a)) (p13 a c)))).trans (cg (fun t => (((a ◇ a) ◇ b) ◇ c) ◇ t) (pr (((a ◇ a) ◇ c) ◇ a) a))).trans (cg (fun t => (((a ◇ a) ◇ b) ◇ c) ◇ t) (p19 c a))).symm).trans (((cg (fun t => (((a ◇ a) ◇ b) ◇ c) ◇ t) (cg (fun t => t ◇ (a ◇ a)) (cg (fun t => t ◇ (a ◇ a)) (cg (fun t => t ◇ (a ◇ a)) (p1b a c b))))).symm).trans (p1o (a ◇ a) (((a ◇ a) ◇ b) ◇ c) c))
  have p21:=fun (a b c:G)=>by
    exact (((p1y a b c).symm).trans ((((cg (fun t => t ◇ ((c ◇ c) ◇ c)) (p1x a b c)).symm).trans (p20 c ((((c ◇ a) ◇ b) ◇ c) ◇ c) ((c ◇ a) ◇ b))).trans (cg (fun t => t ◇ (c ◇ c)) (p1x a b c)))).symm
  have p22:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ (((b ◇ b) ◇ a) ◇ b)) (cg (fun t => t ◇ c) (cg (fun t => t ◇ c) (p1l a b)))).symm).trans ((h (((b ◇ b) ◇ a) ◇ b) c (((b ◇ a) ◇ a) ◇ a)).symm)
  have p23:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (((b ◇ b) ◇ a) ◇ b)) (p1w b a)).trans (p22 a b a)).symm).trans ((((cg (fun t => t ◇ (((b ◇ b) ◇ a) ◇ b)) (cg (fun t => t ◇ (((b ◇ a) ◇ a) ◇ a)) (p1k a b))).symm).trans (p22 a b (((b ◇ a) ◇ a) ◇ a))).trans (p1l a b))
  have p24:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ b) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (py a b))).trans (cg (fun t => t ◇ b) (po b a))).symm).trans (((cg (fun t => t ◇ b) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => t ◇ b) (p3 a a a)))).symm).trans (p23 b ((a ◇ a) ◇ a)))
  have p25:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ a) (p1w a b)).trans (p1j a b)).symm).trans (((cg (fun t => t ◇ a) (cg (fun t => t ◇ (((a ◇ b) ◇ b) ◇ b)) (p1k b a))).symm).trans ((h a (((a ◇ b) ◇ b) ◇ b) b).symm))).symm
  have p26:=fun (a b:G)=>by
    exact ((pd b a a b).symm).trans ((((cg (fun t => (((b ◇ b) ◇ a) ◇ a) ◇ t) (cg (fun t => t ◇ b) (cg (fun t => t ◇ b) (p2 b a a)))).symm).trans (p25 (((b ◇ b) ◇ a) ◇ a) b)).trans (p2 b a ((((b ◇ b) ◇ a) ◇ a) ◇ b)))
  have p27:=fun (a b c:G)=>by
    exact ((p1a a (((a ◇ c) ◇ b) ◇ b) b).symm).trans ((((cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ a)) (cg (fun t => t ◇ (((a ◇ c) ◇ b) ◇ b)) (cg (fun t => t ◇ (((a ◇ c) ◇ b) ◇ b)) (p1a a b c)))).symm).trans (p26 (((a ◇ a) ◇ a) ◇ a) (((a ◇ c) ◇ b) ◇ b))).trans (p1a a b c))
  have p28:=fun (a b:G)=>by
    exact (((p3 a b a).symm).trans (((cg (fun t => ((b ◇ a) ◇ b) ◇ t) (cg (fun t => t ◇ a) (p26 a b))).symm).trans (p27 ((b ◇ a) ◇ b) a b))).symm
  have p29:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ b) (p21 a b a)).symm).trans (((cg (fun t => t ◇ b) (cg (fun t => t ◇ (a ◇ a)) (p1p a a b))).symm).trans (p26 b (a ◇ a)))
  have p2a:=fun (a b c:G)=>by
    exact ((cg (fun t => ((b ◇ a) ◇ c) ◇ t) (cg (fun t => t ◇ b) ((h b c a).symm))).symm).trans (p27 ((b ◇ a) ◇ c) b c)
  have p2b:=fun (a b c:G)=>by
    exact ((pd a b c (c ◇ c)).symm).trans ((((cg (fun t => t ◇ ((((c ◇ c) ◇ b) ◇ a) ◇ a)) (cg (fun t => t ◇ c) (cg (fun t => t ◇ c) (p27 (c ◇ c) a b)))).symm).trans (p29 c ((((c ◇ c) ◇ b) ◇ a) ◇ a))).trans (p27 (c ◇ c) a b))
  have p2c:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ c) (cg (fun t => t ◇ b) (cg (fun t => t ◇ b) (p0 a c)))).symm).trans (p2b b (c ◇ a) c)
  have p2d:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ b) (cg (fun t => t ◇ a) (p28 a b))).symm).trans (p2c a a b)
  have p2e:=fun (a b c:G)=>by
    exact (((cg (fun t => (((b ◇ b) ◇ a) ◇ c) ◇ t) (p2b b c b)).trans (p20 b a c)).symm).trans (((cg (fun t => (((b ◇ b) ◇ a) ◇ c) ◇ t) (cg (fun t => t ◇ b) (cg (fun t => t ◇ b) (cg (fun t => t ◇ b) (p2b c a b))))).symm).trans (p1o b (((b ◇ b) ◇ a) ◇ c) c))
  have p2f:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ ((((b ◇ a) ◇ a) ◇ a) ◇ a)) (pd a a a b)).trans (pd a a a (b ◇ a))).symm).trans ((((cg (fun t => ((((b ◇ a) ◇ a) ◇ a) ◇ (((b ◇ a) ◇ a) ◇ a)) ◇ t) (p1u a b)).symm).trans (p0 ((((b ◇ a) ◇ a) ◇ a) ◇ a) (((b ◇ a) ◇ a) ◇ a))).trans (cg (fun t => t ◇ (((b ◇ a) ◇ a) ◇ a)) (p1w (b ◇ a) a)))).symm
  have p2g:=fun (a b c:G)=>by
    exact (((cg (fun t => ((((b ◇ a) ◇ b) ◇ b) ◇ b) ◇ t) (cg (fun t => t ◇ b) (p1t c a b))).trans (cg (fun t => t ◇ (((b ◇ a) ◇ b) ◇ b)) (pp b a))).symm).trans ((((cg (fun t => t ◇ ((((((b ◇ c) ◇ a) ◇ a) ◇ b) ◇ b) ◇ b)) (cg (fun t => t ◇ b) (cg (fun t => t ◇ b) (cg (fun t => t ◇ b) ((h b a c).symm))))).symm).trans (p2f b (((b ◇ c) ◇ a) ◇ a))).trans ((cg (fun t => t ◇ b) (cg (fun t => t ◇ b) (cg (fun t => t ◇ b) (p1t c a b)))).trans (cg (fun t => t ◇ b) (pp b a))))
  have p2h:=fun (a b:G)=>by
    exact (((((((cg (fun t => t ◇ (b ◇ b)) (cg (fun t => t ◇ ((((b ◇ b) ◇ a) ◇ (b ◇ b)) ◇ (b ◇ b))) (cg (fun t => t ◇ (b ◇ b)) (p0 b b)))).trans (cg (fun t => t ◇ (b ◇ b)) (cg (fun t => (((b ◇ b) ◇ b) ◇ (b ◇ b)) ◇ t) (cg (fun t => t ◇ (b ◇ b)) (p1p b b a))))).trans (cg (fun t => t ◇ (b ◇ b)) (cg (fun t => t ◇ ((((b ◇ b) ◇ a) ◇ b) ◇ (b ◇ b))) (p1p b b b)))).trans (cg (fun t => t ◇ (b ◇ b)) (cg (fun t => (((b ◇ b) ◇ b) ◇ b) ◇ t) (p21 b a b)))).trans (cg (fun t => t ◇ (b ◇ b)) (py b ((((b ◇ b) ◇ a) ◇ b) ◇ b)))).trans (pr ((((b ◇ b) ◇ a) ◇ b) ◇ b) b)).symm).trans ((((cg (fun t => t ◇ (b ◇ b)) (cg (fun t => t ◇ ((((b ◇ b) ◇ a) ◇ (b ◇ b)) ◇ (b ◇ b))) (p2g a (b ◇ b) a))).symm).trans (p1b b ((((b ◇ b) ◇ a) ◇ (b ◇ b)) ◇ (b ◇ b)) (b ◇ b))).trans (((cg (fun t => (b ◇ b) ◇ t) (cg (fun t => t ◇ (b ◇ b)) (p1p b b a))).trans (cg (fun t => (b ◇ b) ◇ t) (p21 b a b))).trans (p27 (b ◇ b) b a)))
  have p2i:=fun (a b c:G)=>by
    exact (((((((cg (fun t => t ◇ (((((((a ◇ c) ◇ a) ◇ b) ◇ b) ◇ (a ◇ a)) ◇ (a ◇ a)) ◇ (a ◇ a))) (cg (fun t => t ◇ (a ◇ a)) (cg (fun t => t ◇ (a ◇ a)) (p1p a a b)))).trans (cg (fun t => (((((a ◇ a) ◇ b) ◇ a) ◇ (a ◇ a)) ◇ (a ◇ a)) ◇ t) (cg (fun t => t ◇ (a ◇ a)) (cg (fun t => t ◇ (a ◇ a)) (pa c a b))))).trans (cg (fun t => (((((a ◇ a) ◇ b) ◇ a) ◇ (a ◇ a)) ◇ (a ◇ a)) ◇ t) (cg (fun t => t ◇ (a ◇ a)) (p1p a a b)))).trans (cg (fun t => t ◇ ((((a ◇ a) ◇ b) ◇ a) ◇ (a ◇ a))) (cg (fun t => t ◇ (a ◇ a)) (p21 a b a)))).trans (cg (fun t => (((((a ◇ a) ◇ b) ◇ a) ◇ a) ◇ (a ◇ a)) ◇ t) (p21 a b a))).trans (cg (fun t => t ◇ ((((a ◇ a) ◇ b) ◇ a) ◇ a)) (p1b a a b))).symm).trans ((((cg (fun t => t ◇ (((((((a ◇ c) ◇ a) ◇ b) ◇ b) ◇ (a ◇ a)) ◇ (a ◇ a)) ◇ (a ◇ a))) (cg (fun t => t ◇ (a ◇ a)) (cg (fun t => t ◇ (a ◇ a)) (cg (fun t => t ◇ (a ◇ a)) (pa c a b))))).symm).trans (p2f (a ◇ a) ((((a ◇ c) ◇ a) ◇ b) ◇ b))).trans (((((cg (fun t => t ◇ (a ◇ a)) (cg (fun t => t ◇ (a ◇ a)) (cg (fun t => t ◇ (a ◇ a)) (cg (fun t => t ◇ (a ◇ a)) (pa c a b))))).trans (cg (fun t => t ◇ (a ◇ a)) (cg (fun t => t ◇ (a ◇ a)) (cg (fun t => t ◇ (a ◇ a)) (p1p a a b))))).trans (cg (fun t => t ◇ (a ◇ a)) (cg (fun t => t ◇ (a ◇ a)) (p21 a b a)))).trans (cg (fun t => t ◇ (a ◇ a)) (p1b a a b))).trans (p1p a a a)))
  have p2j:=fun (a b:G)=>by
    exact ((((((((cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => t ◇ ((((a ◇ a) ◇ b) ◇ a) ◇ a)) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (py a ((((a ◇ a) ◇ b) ◇ a) ◇ a))))).trans (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => t ◇ ((((a ◇ a) ◇ b) ◇ a) ◇ a)) (po ((((a ◇ a) ◇ b) ◇ a) ◇ a) a)))).trans (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => t ◇ ((((a ◇ a) ◇ b) ◇ a) ◇ a)) (p2h b a)))).trans (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (p2i a b (((a ◇ a) ◇ a) ◇ ((((a ◇ a) ◇ b) ◇ a) ◇ a))))).trans (py a ((a ◇ a) ◇ a))).trans (p8 a)).symm).trans ((((cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => t ◇ ((((a ◇ a) ◇ b) ◇ a) ◇ a)) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => t ◇ ((((a ◇ a) ◇ b) ◇ a) ◇ a)) (p2i a b a))))).symm).trans (p2d ((((a ◇ a) ◇ b) ◇ a) ◇ a) ((a ◇ a) ◇ a))).trans ((cg (fun t => t ◇ ((((a ◇ a) ◇ b) ◇ a) ◇ a)) (p3 a a a)).trans (py a ((((a ◇ a) ◇ b) ◇ a) ◇ a))))).symm
  have p2k:=fun (a b:G)=>by
    exact ((cg (fun t => a ◇ t) (p18 b a)).symm).trans (p2j a b)
  have p2l:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ (((b ◇ b) ◇ c) ◇ (b ◇ a))) (p1p a b b)).symm).trans ((((cg (fun t => t ◇ (((b ◇ b) ◇ c) ◇ (b ◇ a))) (cg (fun t => t ◇ (b ◇ b)) (p0 a b))).symm).trans (p3 c (b ◇ b) (b ◇ a))).trans (p2e c b (b ◇ a)))
  have p2m:=fun (a b:G)=>by
    exact ((cg (fun t => ((a ◇ a) ◇ a) ◇ t) (p18 b a)).symm).trans (p2i a b a)
  have p2n:=fun (a b:G)=>by
    exact ((((cg (fun t => (((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => (((a ◇ a) ◇ b) ◇ a) ◇ t) (p1z a b))).trans (cg (fun t => t ◇ ((((a ◇ a) ◇ b) ◇ a) ◇ (((a ◇ a) ◇ b) ◇ a))) (p3 a a a))).trans (py a ((((a ◇ a) ◇ b) ◇ a) ◇ (((a ◇ a) ◇ b) ◇ a)))).symm).trans ((((cg (fun t => (((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ (((a ◇ a) ◇ b) ◇ ((a ◇ a) ◇ b)))) (p1z a b))).symm).trans (ps (((a ◇ a) ◇ b) ◇ ((a ◇ a) ◇ b)) ((a ◇ a) ◇ a))).trans ((cg (fun t => t ◇ ((a ◇ a) ◇ a)) (p1z a b)).trans (p1y a b a)))
  have p2o:=fun (a b c:G)=>by
    exact (((((((cg (fun t => t ◇ (((b ◇ c) ◇ b) ◇ b)) (cg (fun t => t ◇ (b ◇ ((((b ◇ b) ◇ a) ◇ b) ◇ (((b ◇ b) ◇ a) ◇ b)))) (p2b b a b))).trans (cg (fun t => t ◇ (((b ◇ c) ◇ b) ◇ b)) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (p2n b a)))).trans (cg (fun t => t ◇ (((b ◇ c) ◇ b) ◇ b)) (p2i b a (((b ◇ b) ◇ b) ◇ ((((b ◇ b) ◇ a) ◇ b) ◇ b))))).trans (pd b c b b)).trans (pp b c)).symm).trans ((((cg (fun t => t ◇ (((b ◇ c) ◇ b) ◇ b)) (cg (fun t => t ◇ (b ◇ ((((b ◇ b) ◇ a) ◇ b) ◇ (((b ◇ b) ◇ a) ◇ b)))) (cg (fun t => t ◇ b) (p2n b a)))).symm).trans (p1g ((((b ◇ b) ◇ a) ◇ b) ◇ (((b ◇ b) ◇ a) ◇ b)) b c)).trans (cg (fun t => (((b ◇ c) ◇ b) ◇ b) ◇ t) (p2n b a)))).symm
  have p2p:=fun (a b c:G)=>by
    exact ((((cg (fun t => t ◇ ((c ◇ b) ◇ c)) (p27 (c ◇ c) c a)).trans (p3 b c c)).symm).trans (((cg (fun t => t ◇ ((c ◇ b) ◇ c)) (cg (fun t => t ◇ ((((c ◇ c) ◇ a) ◇ c) ◇ c)) (p2o a c b))).symm).trans ((h ((c ◇ b) ◇ c) ((((c ◇ c) ◇ a) ◇ c) ◇ c) c).symm))).symm
  have p2q:=fun (a b c:G)=>by
    exact ((((cg (fun t => t ◇ (c ◇ b)) (p2o a c b)).trans (p0 b c)).symm).trans (((cg (fun t => t ◇ (c ◇ b)) (cg (fun t => t ◇ ((((c ◇ c) ◇ a) ◇ c) ◇ c)) (p2p a b c))).symm).trans ((h (c ◇ b) ((((c ◇ c) ◇ a) ◇ c) ◇ c) c).symm))).symm
  have p2r:=fun (a b c:G)=>by
    exact ((cg (fun t => (c ◇ b) ◇ t) (p18 a c)).symm).trans (p2q a b c)
  have p2s:=fun (a b c:G)=>by
    exact ((((((cg (fun t => t ◇ c) (cg (fun t => t ◇ (b ◇ (((b ◇ b) ◇ a) ◇ b))) (cg (fun t => t ◇ (b ◇ (((b ◇ b) ◇ a) ◇ b))) (p19 a b)))).trans (cg (fun t => t ◇ c) (cg (fun t => t ◇ (b ◇ (((b ◇ b) ◇ a) ◇ b))) (p2m b a)))).trans (cg (fun t => t ◇ c) (py b (b ◇ (((b ◇ b) ◇ a) ◇ b))))).trans (cg (fun t => t ◇ c) (p2k b a))).symm).trans (((cg (fun t => t ◇ c) (cg (fun t => t ◇ (b ◇ (((b ◇ b) ◇ a) ◇ b))) (cg (fun t => t ◇ (b ◇ (((b ◇ b) ◇ a) ◇ b))) (p2r a (((b ◇ b) ◇ a) ◇ b) b)))).symm).trans (py (b ◇ (((b ◇ b) ◇ a) ◇ b)) c))).symm
  have p2t:=fun (a b c:G)=>by
    exact ((((cg (fun t => t ◇ c) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (py a b)))).trans (cg (fun t => t ◇ c) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (po b a)))).trans (cg (fun t => t ◇ c) (p3 b a a))).symm).trans ((((cg (fun t => t ◇ c) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => t ◇ b) (p3 a a a))))).symm).trans (p2s b ((a ◇ a) ◇ a) c)).trans ((cg (fun t => t ◇ c) (p3 a a a)).trans (py a c)))
  have p2u:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ b) (p2t b a ((b ◇ a) ◇ b))).symm).trans (p24 ((b ◇ a) ◇ b) b)).trans ((p1v b (b ◇ a)).trans (cg (fun t => t ◇ ((b ◇ a) ◇ b)) (p2t b a b)))
  have p2v:=fun (a b c:G)=>by
    exact (((p2t b a (((b ◇ b) ◇ c) ◇ (b ◇ a))).symm).trans (p2l a b c)).symm
  have p2w:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ b) (p23 (((b ◇ b) ◇ a) ◇ b) b)).trans (p2s a b b)).symm).trans (((cg (fun t => t ◇ b) (cg (fun t => t ◇ (((b ◇ b) ◇ a) ◇ b)) (cg (fun t => t ◇ b) (p2s a b (((b ◇ b) ◇ a) ◇ b))))).symm).trans (p2d (((b ◇ b) ◇ a) ◇ b) b))).symm
  have p2x:=fun (a b:G)=>by
    exact (((((cg (fun t => (((a ◇ a) ◇ a) ◇ a) ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => t ◇ b) (p3 a a a)))).trans (cg (fun t => (((a ◇ a) ◇ a) ◇ a) ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (p2t a a b)))).trans (cg (fun t => (((a ◇ a) ◇ a) ◇ a) ◇ t) (po b a))).trans (p2t a a ((a ◇ b) ◇ a))).symm).trans ((((cg (fun t => t ◇ (((((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ b) ◇ ((a ◇ a) ◇ a))) (p3 a a a)).symm).trans (p2w b ((a ◇ a) ◇ a))).trans (((cg (fun t => t ◇ ((a ◇ a) ◇ a)) (p3 a a a)).trans (p1d a a a)).trans (p2 a a ((((a ◇ a) ◇ a) ◇ a) ◇ a))))
  have p2y:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ b) (p2x b a)).symm).trans (p2u a b)).symm
  have p2z:=fun (a b:G)=>by
    exact ((((((cg (fun t => ((b ◇ b) ◇ b) ◇ t) (cg (fun t => t ◇ ((b ◇ a) ◇ b)) (cg (fun t => t ◇ ((b ◇ a) ◇ b)) (p2y a b)))).trans (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (cg (fun t => t ◇ ((b ◇ a) ◇ b)) (p3 a b b)))).trans (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (p2t b a ((b ◇ a) ◇ b)))).trans (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (p2x b a))).trans (p1p b b b)).symm).trans ((((cg (fun t => t ◇ ((((b ◇ b) ◇ ((b ◇ a) ◇ b)) ◇ ((b ◇ a) ◇ b)) ◇ ((b ◇ a) ◇ b))) (p2y a b)).symm).trans (p1k ((b ◇ a) ◇ b) (b ◇ b))).trans ((cg (fun t => t ◇ ((b ◇ a) ◇ b)) (p2y a b)).trans (p3 a b b)))
  have p30:=fun (a b c:G)=>by
    exact ((((cg (fun t => t ◇ c) (cg (fun t => t ◇ ((b ◇ a) ◇ b)) (p2t b b ((b ◇ a) ◇ b)))).trans (cg (fun t => t ◇ c) (cg (fun t => t ◇ ((b ◇ a) ◇ b)) (p2x b a)))).trans (cg (fun t => t ◇ c) (p2y a b))).symm).trans (((cg (fun t => t ◇ c) (cg (fun t => t ◇ ((b ◇ a) ◇ b)) (cg (fun t => t ◇ ((b ◇ a) ◇ b)) ((p2z a b).symm)))).symm).trans (p2t ((b ◇ a) ◇ b) b c))
  have p31:=fun (a b:G)=>by
    exact (((((cg (fun t => t ◇ a) (cg (fun t => t ◇ (a ◇ a)) (p0 a a))).trans (cg (fun t => t ◇ a) (p1p a a a))).trans (p2 a a ((((a ◇ a) ◇ a) ◇ a) ◇ a))).symm).trans (((p30 b (a ◇ a) a).trans (p2v a a b)).trans (cg (fun t => a ◇ t) (p1p a a b)))).symm
  have p32:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ (((c ◇ a) ◇ c) ◇ (c ◇ a))) (cg (fun t => t ◇ b) (cg (fun t => t ◇ b) (p4 a c)))).symm).trans ((h (((c ◇ a) ◇ c) ◇ (c ◇ a)) b c).symm)
  have p33:=fun (a b:G)=>by
    exact (((((cg (fun t => t ◇ (b ◇ (b ◇ a))) (p2t b a ((b ◇ a) ◇ b))).trans (cg (fun t => t ◇ (b ◇ (b ◇ a))) (p2x b a))).trans (p0 (b ◇ a) b)).symm).trans ((((cg (fun t => ((((b ◇ a) ◇ b) ◇ b) ◇ ((b ◇ a) ◇ b)) ◇ t) (p4 a b)).symm).trans (p3 (b ◇ a) ((b ◇ a) ◇ b) b)).trans (cg (fun t => t ◇ ((b ◇ a) ◇ b)) (p4 a b)))).symm
  have p34:=fun (a b:G)=>by
    exact (((((cg (fun t => t ◇ (((b ◇ a) ◇ b) ◇ (b ◇ a))) (pb a b)).trans (p2a b (b ◇ a) b)).trans (p2t b a (b ◇ a))).symm).trans (((cg (fun t => t ◇ (((b ◇ a) ◇ b) ◇ (b ◇ a))) (cg (fun t => t ◇ ((b ◇ a) ◇ b)) (p33 a b))).symm).trans (p32 a ((b ◇ a) ◇ b) b))).symm
  have p35:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (b ◇ a)) (p34 a b)).symm).trans (p4 b (b ◇ a))
  have p36:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ c) (p33 a b)).symm).trans (((cg (fun t => t ◇ c) (cg (fun t => t ◇ ((b ◇ a) ◇ b)) (p34 a b))).symm).trans (p2t ((b ◇ a) ◇ b) (b ◇ a) c))
  have p37:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ b) (p35 a (b ◇ c))).symm).trans ((h b ((b ◇ c) ◇ a) c).symm)
  have p38:=fun (a b:G)=>by
    exact ((cg (fun t => ((b ◇ a) ◇ ((b ◇ a) ◇ b)) ◇ t) (pr a b)).symm).trans ((((cg (fun t => t ◇ ((b ◇ a) ◇ (b ◇ b))) (cg (fun t => (b ◇ a) ◇ t) (pr a b))).symm).trans (p35 (b ◇ b) (b ◇ a))).trans ((cg (fun t => ((b ◇ a) ◇ (b ◇ b)) ◇ t) (cg (fun t => t ◇ (b ◇ a)) (pr a b))).trans (cg (fun t => t ◇ (((b ◇ a) ◇ b) ◇ (b ◇ a))) (pr a b))))
  have p39:=fun (a b:G)=>by
    exact ((((cg (fun t => ((((b ◇ a) ◇ b) ◇ (((b ◇ a) ◇ b) ◇ (b ◇ a))) ◇ ((b ◇ a) ◇ b)) ◇ t) (p34 a b)).trans (p36 (b ◇ a) ((b ◇ a) ◇ b) (b ◇ (b ◇ a)))).trans (cg (fun t => t ◇ (b ◇ (b ◇ a))) (p34 a b))).symm).trans ((((cg (fun t => t ◇ ((((b ◇ a) ◇ b) ◇ (b ◇ a)) ◇ ((b ◇ a) ◇ b))) (cg (fun t => t ◇ ((b ◇ a) ◇ b)) (p38 a b))).symm).trans (p32 b ((b ◇ a) ◇ b) (b ◇ a))).trans ((cg (fun t => t ◇ ((b ◇ a) ◇ b)) (p34 a b)).trans (p33 a b)))
  have p3a:=fun (a b:G)=>by
    exact (((p2x b (b ◇ a)).symm).trans (((cg (fun t => b ◇ t) (p39 a b)).symm).trans (pi b (b ◇ a)))).symm
  have p3b:=fun (a b:G)=>by
    exact (((p2y (b ◇ a) b).symm).trans (((cg (fun t => (b ◇ b) ◇ t) (p39 a b)).symm).trans (ps (b ◇ a) b))).symm
  have p3c:=fun (a b c:G)=>by
    exact (((((cg (fun t => t ◇ b) (po ((b ◇ c) ◇ a) (b ◇ c))).trans (cg (fun t => t ◇ b) (p3b a (b ◇ c)))).trans (pj b c)).symm).trans (((cg (fun t => t ◇ b) (cg (fun t => ((b ◇ c) ◇ ((b ◇ c) ◇ a)) ◇ t) (p3b a (b ◇ c)))).symm).trans (p37 ((b ◇ c) ◇ a) b c))).symm
  have p3d:=fun (a b:G)=>by
    exact (((p1k b a).symm).trans (((cg (fun t => (a ◇ b) ◇ t) (p1w a b)).symm).trans (p3c b (a ◇ b) b))).symm
  have p3e:=fun (a b:G)=>by
    exact (((p3d a b).symm).trans (((cg (fun t => (a ◇ b) ◇ t) (p3d a b)).symm).trans (p3a b (a ◇ b)))).symm
  have p3f:=fun (a b:G)=>by
    exact ((((cg (fun t => (b ◇ a) ◇ t) (p2 b a ((((b ◇ b) ◇ a) ◇ a) ◇ b))).trans (p3e b a)).symm).trans ((((cg (fun t => t ◇ ((((b ◇ b) ◇ a) ◇ a) ◇ b)) (p2 b a a)).symm).trans (p3e (((b ◇ b) ◇ a) ◇ a) b)).trans (cg (fun t => t ◇ b) (p2 b a ((((b ◇ b) ◇ a) ◇ a) ◇ b))))).symm
  have p3g:=fun (a b:G)=>by
    exact ((p2 a b ((((a ◇ a) ◇ b) ◇ b) ◇ a)).symm).trans ((((cg (fun t => t ◇ a) (p3f b (a ◇ a))).symm).trans (p2v a a b)).trans ((cg (fun t => a ◇ t) (p1p a a b)).trans (p31 a b)))
  exact (p3g x x).trans ((p3g x y).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_53228_to_38 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_53228_to_38
