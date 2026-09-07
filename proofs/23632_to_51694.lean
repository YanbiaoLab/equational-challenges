-- Equation23632 → Equation51694
-- Recorded verdict: false
-- Premise: x = ((y ◇ z) ◇ x) ◇ (x ◇ (w ◇ w))
-- Conclusion: x ◇ y = ((z ◇ x) ◇ (x ◇ w)) ◇ y
-- Original submission SHA-256: 061f8059d0494da060dc709ecb6b2b330414be0d1476198d17dbc85872beb820
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ z) ◇ x) ◇ (x ◇ (w ◇ w))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ x) ◇ (x ◇ w)) ◇ y
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Original submission body
-- stage:stage0_generalized_infinite_source_family
-- d14-direct-template
                   
set_option maxRecDepth 100000
namespace submission
inductive Raw where
  | e : Raw
  | p : Raw → Raw → Raw
deriving DecidableEq
namespace Raw
def sq (a : Raw) : Raw := p a a
def q (a b : Raw) : Raw := p (sq a) b
def nodes : Raw → Nat
  | e => 0
  | p a b => nodes a + nodes b + 1
theorem nodes_lt_p_left (a b : Raw) : nodes a < nodes (p a b) := by
  simp [nodes] <;> omega
theorem nodes_lt_p_right (a b : Raw) : nodes b < nodes (p a b) := by
  simp [nodes] <;> omega
def try0 : Raw → Option Raw
  | p (p (p y₁ y₂) x₁) (p x₂ _) =>
      if y₁ = y₂ ∧ x₁ = x₂ then some x₁ else none
  | _ => none
def try1 : Raw → Option Raw
  | p (p (p y₁ y₂) (p (p a₁ a₂) x₁)) x₂ =>
      if y₁ = y₂ ∧ a₁ = a₂ ∧ x₁ = x₂
      then some (q a₁ x₁) else none
  | _ => none
def try2 : Raw → Option Raw
  | p (p y₁ y₂) (p (p (p v₁ v₂) x) _) =>
      if y₁ = y₂ ∧ v₁ = v₂ ∧ y₁ = v₁
      then some (q y₁ x) else none
  | _ => none
def try3 : Raw → Option Raw
  | p (p (p y₁ y₂) x₁)
      (p (p (p (p v₁ v₂) x₂) a) _) =>
      if y₁ = y₂ ∧ v₁ = v₂ ∧ y₁ = v₁ ∧ x₁ = x₂
      then some (p (q y₁ x₁) a) else none
  | _ => none
def lhs0 (y x a : Raw) : Raw := p (q y x) (p x a)
def lhs1 (y a x : Raw) : Raw := p (q y (q a x)) x
def lhs2 (y x b : Raw) : Raw := p (sq y) (p (q y x) b)
def lhs3 (y x a b : Raw) : Raw :=
  p (q y x) (p (p (q y x) a) b)
theorem try0_sound {t u : Raw} (h : try0 t = some u) :
    ∃ y x a, t = lhs0 y x a ∧ u = x := by
  cases t with
  | e => simp [try0] at h
  | p l r =>
    cases l with
    | e => simp [try0] at h
    | p ll x =>
      cases ll with
      | e => simp [try0] at h
      | p y₁ y₂ =>
        cases r with
        | e => simp [try0] at h
        | p x₂ a =>
          by_cases hc : y₁ = y₂ ∧ x = x₂
          · rw [try0, if_pos hc] at h
            have hu : x = u := Option.some.inj h
            exact ⟨y₁, x, a, by simp [lhs0, q, sq, hc], hu.symm⟩
          · simp [try0, hc] at h
theorem try1_sound {t u : Raw} (h : try1 t = some u) :
    ∃ y a x, t = lhs1 y a x ∧ u = q a x := by
  cases t with
  | e => simp [try1] at h
  | p l x₂ =>
    cases l with
    | e => simp [try1] at h
    | p ll ar =>
      cases ll with
      | e => simp [try1] at h
      | p y₁ y₂ =>
        cases ar with
        | e => simp [try1] at h
        | p aar x₁ =>
          cases aar with
          | e => simp [try1] at h
          | p a₁ a₂ =>
            by_cases hc : y₁ = y₂ ∧ a₁ = a₂ ∧ x₁ = x₂
            · rw [try1, if_pos hc] at h
              have hu : q a₁ x₁ = u := Option.some.inj h
              exact ⟨y₁, a₁, x₁,
                by simp [lhs1, q, sq, hc], hu.symm⟩
            · simp [try1, hc] at h
theorem try2_sound {t u : Raw} (h : try2 t = some u) :
    ∃ y x b, t = lhs2 y x b ∧ u = q y x := by
  cases t with
  | e => simp [try2] at h
  | p l r =>
    cases l with
    | e => simp [try2] at h
    | p y₁ y₂ =>
      cases r with
      | e => simp [try2] at h
      | p rl b =>
        cases rl with
        | e => simp [try2] at h
        | p rll x =>
          cases rll with
          | e => simp [try2] at h
          | p v₁ v₂ =>
            by_cases hc : y₁ = y₂ ∧ v₁ = v₂ ∧ y₁ = v₁
            · rw [try2, if_pos hc] at h
              have hu : q y₁ x = u := Option.some.inj h
              have hv₂y₂ : v₂ = y₂ :=
                hc.2.1.symm.trans (hc.2.2.symm.trans hc.1)
              exact ⟨y₁, x, b,
                by simp [lhs2, q, sq, hc, hv₂y₂], hu.symm⟩
            · simp [try2, hc] at h
theorem try3_sound {t u : Raw} (h : try3 t = some u) :
    ∃ y x a b, t = lhs3 y x a b ∧ u = p (q y x) a := by
  cases t with
  | e => simp [try3] at h
  | p l r =>
    cases l with
    | e => simp [try3] at h
    | p ll x₁ =>
      cases ll with
      | e => simp [try3] at h
      | p y₁ y₂ =>
        cases r with
        | e => simp [try3] at h
        | p rl b =>
          cases rl with
          | e => simp [try3] at h
          | p rll a =>
            cases rll with
            | e => simp [try3] at h
            | p rlll x₂ =>
              cases rlll with
              | e => simp [try3] at h
              | p v₁ v₂ =>
                by_cases hc :
                    y₁ = y₂ ∧ v₁ = v₂ ∧ y₁ = v₁ ∧ x₁ = x₂
                · rw [try3, if_pos hc] at h
                  have hu : p (q y₁ x₁) a = u :=
                    Option.some.inj h
                  have hv₂y₂ : v₂ = y₂ :=
                    hc.2.1.symm.trans (hc.2.2.1.symm.trans hc.1)
                  exact ⟨y₁, x₁, a, b,
                    by simp [lhs3, q, sq, hc, hv₂y₂], hu.symm⟩
                · simp [try3, hc] at h
def root (t : Raw) : Option Raw :=
  match try0 t with
  | some u => some u
  | none =>
    match try1 t with
    | some u => some u
    | none =>
      match try2 t with
      | some u => some u
      | none => try3 t
def rawOp (a b : Raw) : Raw :=
  (root (p a b)).getD (p a b)
inductive Step : Raw → Raw → Prop where
  | rule0 (y x a) : Step (lhs0 y x a) x
  | rule1 (y a x) (miss0 : try0 (lhs1 y a x) = none) :
      Step (lhs1 y a x) (q a x)
  | rule2 (y x b) (miss0 : try0 (lhs2 y x b) = none)
      (miss1 : try1 (lhs2 y x b) = none) :
      Step (lhs2 y x b) (q y x)
  | rule3 (y x a b) (miss0 : try0 (lhs3 y x a b) = none)
      (miss1 : try1 (lhs3 y x a b) = none)
      (miss2 : try2 (lhs3 y x a b) = none) :
      Step (lhs3 y x a b) (p (q y x) a)
  | raw (t) (miss0 : try0 t = none) (miss1 : try1 t = none)
      (miss2 : try2 t = none) (miss3 : try3 t = none) : Step t t
def StepCases (t u : Raw) : Prop :=
  (∃ y x a, t = lhs0 y x a ∧ u = x) ∨
  (∃ y a x, t = lhs1 y a x ∧ u = q a x ∧
    try0 t = none) ∨
  (∃ y x b, t = lhs2 y x b ∧ u = q y x ∧
    try0 t = none ∧ try1 t = none) ∨
  (∃ y x a b, t = lhs3 y x a b ∧ u = p (q y x) a ∧
    try0 t = none ∧ try1 t = none ∧ try2 t = none) ∨
  (t = u ∧ try0 t = none ∧ try1 t = none ∧
    try2 t = none ∧ try3 t = none)
theorem step_cases {t u : Raw} (h : Step t u) : StepCases t u := by
  cases h with
  | rule0 y x a =>
    exact Or.inl ⟨y, _, a, rfl, rfl⟩
  | rule1 y a x m0 =>
    exact Or.inr (Or.inl ⟨y, a, x, rfl, rfl, m0⟩)
  | rule2 y x b m0 m1 =>
    exact Or.inr (Or.inr (Or.inl
      ⟨y, x, b, rfl, rfl, m0, m1⟩))
  | rule3 y x a b m0 m1 m2 =>
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨y, x, a, b, rfl, rfl, m0, m1, m2⟩)))
  | raw t m0 m1 m2 m3 =>
    exact Or.inr (Or.inr (Or.inr (Or.inr
      ⟨rfl, m0, m1, m2, m3⟩)))
theorem rawOp_step (a b : Raw) : Step (p a b) (rawOp a b) := by
  unfold rawOp root
  cases h0 : try0 (p a b) with
  | some u =>
    obtain ⟨y, x, c, ht, hu⟩ := try0_sound h0
    have hs : Step (p a b) u := by
      rw [ht, hu]
      exact Step.rule0 y x c
    simpa [h0] using hs
  | none =>
    cases h1 : try1 (p a b) with
    | some u =>
      obtain ⟨y, c, x, ht, hu⟩ := try1_sound h1
      have m0 : try0 (lhs1 y c x) = none := by
        rw [← ht]
        exact h0
      have hs : Step (p a b) u := by
        rw [ht, hu]
        exact Step.rule1 y c x m0
      simpa [h0, h1] using hs
    | none =>
      cases h2 : try2 (p a b) with
      | some u =>
        obtain ⟨y, x, c, ht, hu⟩ := try2_sound h2
        have m0 : try0 (lhs2 y x c) = none := by
          rw [← ht]
          exact h0
        have m1 : try1 (lhs2 y x c) = none := by
          rw [← ht]
          exact h1
        have hs : Step (p a b) u := by
          rw [ht, hu]
          exact Step.rule2 y x c m0 m1
        simpa [h0, h1, h2] using hs
      | none =>
        cases h3 : try3 (p a b) with
        | some u =>
          obtain ⟨y, x, c, d, ht, hu⟩ := try3_sound h3
          have m0 : try0 (lhs3 y x c d) = none := by
            rw [← ht]
            exact h0
          have m1 : try1 (lhs3 y x c d) = none := by
            rw [← ht]
            exact h1
          have m2 : try2 (lhs3 y x c d) = none := by
            rw [← ht]
            exact h2
          have hs : Step (p a b) u := by
            rw [ht, hu]
            exact Step.rule3 y x c d m0 m1 m2
          simpa [h0, h1, h2, h3] using hs
        | none =>
          simpa [h0, h1, h2, h3] using
            Step.raw (p a b) h0 h1 h2 h3
def NF : Raw → Prop
  | e => True
  | p a b => NF a ∧ NF b ∧ root (p a b) = none
theorem try0_nf {a b u : Raw} (ha : NF a)
    (h : try0 (p a b) = some u) : NF u := by
  cases a with
  | e => simp [try0] at h
  | p al ar =>
    cases al with
    | e => simp [try0] at h
    | p y₁ y₂ =>
      cases b with
      | e => simp [try0] at h
      | p x₂ tail =>
        by_cases hc : y₁ = y₂ ∧ ar = x₂
        · simp [try0, hc] at h
          subst u
          simpa [hc.2] using ha.2.1
        · simp [try0, hc] at h
theorem try1_nf {a b u : Raw} (ha : NF a)
    (h : try1 (p a b) = some u) : NF u := by
  cases a with
  | e => simp [try1] at h
  | p al ar =>
    cases al with
    | e => simp [try1] at h
    | p y₁ y₂ =>
      cases ar with
      | e => simp [try1] at h
      | p aar x₁ =>
        cases aar with
        | e => simp [try1] at h
        | p a₁ a₂ =>
          by_cases hc : y₁ = y₂ ∧ a₁ = a₂ ∧ x₁ = b
          · simp [try1, hc] at h
            subst u
            rcases hc with ⟨rfl, rfl, rfl⟩
            simpa [q, sq] using ha.2.1
          · simp [try1, hc] at h
theorem try2_nf {a b u : Raw} (hb : NF b)
    (h : try2 (p a b) = some u) : NF u := by
  cases a with
  | e => simp [try2] at h
  | p y₁ y₂ =>
    cases b with
    | e => simp [try2] at h
    | p bl tail =>
      cases bl with
      | e => simp [try2] at h
      | p bll x =>
        cases bll with
        | e => simp [try2] at h
        | p v₁ v₂ =>
          by_cases hc : y₁ = y₂ ∧ v₁ = v₂ ∧ y₁ = v₁
          · simp [try2, hc] at h
            rcases h with ⟨hyv, rfl⟩
            rcases hc with ⟨_, hv, _⟩
            simpa [q, sq, hyv, hv] using hb.1
          · simp [try2, hc] at h
theorem try3_nf {a b u : Raw} (hb : NF b)
    (h : try3 (p a b) = some u) : NF u := by
  cases a with
  | e => simp [try3] at h
  | p al x₁ =>
    cases al with
    | e => simp [try3] at h
    | p y₁ y₂ =>
      cases b with
      | e => simp [try3] at h
      | p bl tail =>
        cases bl with
        | e => simp [try3] at h
        | p bll aa =>
          cases bll with
          | e => simp [try3] at h
          | p blll x₂ =>
            cases blll with
            | e => simp [try3] at h
            | p v₁ v₂ =>
              by_cases hc :
                  y₁ = y₂ ∧ v₁ = v₂ ∧ y₁ = v₁ ∧ x₁ = x₂
              · simp [try3, hc] at h
                rcases h with ⟨hyv, rfl⟩
                rcases hc with ⟨_, hv, _, _⟩
                simpa [q, sq, hyv, hv] using hb.1
              · simp [try3, hc] at h
theorem root_nf {a b u : Raw} (ha : NF a) (hb : NF b)
    (h : root (p a b) = some u) : NF u := by
  unfold root at h
  split at h
  · simp_all only [Option.some.injEq]
    exact try0_nf ha ‹try0 (p a b) = some u›
  · split at h
    · simp_all only [Option.some.injEq]
      exact try1_nf ha ‹try1 (p a b) = some u›
    · split at h
      · simp_all only [Option.some.injEq]
        exact try2_nf hb ‹try2 (p a b) = some u›
      · exact try3_nf hb h
theorem rawOp_nf {a b : Raw} (ha : NF a) (hb : NF b) :
    NF (rawOp a b) := by
  unfold rawOp
  cases h : root (p a b) with
  | none => simp [NF, ha, hb, h]
  | some u => simpa [h] using root_nf ha hb h
def Carrier := {t : Raw // NF t}
def op (a b : Carrier) : Carrier :=
  ⟨rawOp a.1 b.1, rawOp_nf a.2 b.2⟩
instance instMagma : Magma Carrier where
  op := op
theorem lhs2_not_nf (y x b : Raw) : ¬ NF (lhs2 y x b) := by
  intro hnf
  have hr : root (lhs2 y x b) = none := hnf.2.2
  unfold root at hr
  cases h0 : try0 (lhs2 y x b) with
  | some u => simp [h0] at hr
  | none =>
    cases h1 : try1 (lhs2 y x b) with
    | some u => simp [h0, h1] at hr
    | none =>
      have h2 : try2 (lhs2 y x b) = some (q y x) := by
        simp [try2, lhs2, q, sq]
      simp [h0, h1, h2] at hr
theorem step_self_square {y yy : Raw} (h : Step (p y y) yy) :
    ∃ k, yy = sq k := by
  have c := step_cases h
  clear h
  rcases c with c0 | c1 | c2 | c3 | c4
  · rcases c0 with ⟨a, x, b, ht, hu⟩
    refine ⟨a, ?_⟩
    grind [lhs0, q, sq]
  · rcases c1 with ⟨a, b, x, ht, hu, hm0⟩
    exfalso
    grind [lhs1, q, sq, nodes_lt_p_left, nodes_lt_p_right]
  · rcases c2 with ⟨a, x, b, ht, hu, hm0, hm1⟩
    exfalso
    grind [lhs2, q, sq, nodes_lt_p_left, nodes_lt_p_right]
  · rcases c3 with ⟨a, x, b, d, ht, hu, hm0, hm1, hm2⟩
    exfalso
    grind [lhs3, q, sq, nodes_lt_p_left, nodes_lt_p_right]
  · rcases c4 with ⟨ht, hm0, hm1, hm2, hm3⟩
    exact ⟨y, by simpa [sq] using ht.symm⟩
theorem step_source_kernel
    {k x zw yx xzw out : Raw}
    (hx : NF x) (hkk_nf : NF (sq k))
    (hyx_nf : NF yx) (hzw_nf : NF zw) (hxzw_nf : NF xzw)
    (hyx : Step (p (sq k) x) yx)
    (hxzw : Step (p x zw) xzw)
    (hout : Step (p yx xzw) out) :
    out = x := by
  have cyx := step_cases hyx
  have cxzw := step_cases hxzw
  have cout := step_cases hout
  clear hyx hxzw hout
  rcases cout with c0 | c1 | c2 | c3 | c4
  · rcases c0 with ⟨yo, xo, ao, hto, huo⟩
    grind (config := { splits := 12, gen := 10 })
      [StepCases, NF, root, try0, try1, try2, try3, lhs0, lhs1,
        lhs2, lhs3, q, sq, lhs2_not_nf,
        nodes_lt_p_left, nodes_lt_p_right]
  · rcases c1 with ⟨yo, ao, xo, hto, huo, hm0o⟩
    grind (config := { splits := 12, gen := 10 })
      [StepCases, NF, root, try0, try1, try2, try3, lhs0, lhs1,
        lhs2, lhs3, q, sq, lhs2_not_nf,
        nodes_lt_p_left, nodes_lt_p_right]
  · rcases c2 with ⟨yo, xo, bo, hto, huo, hm0o, hm1o⟩
    grind (config := { splits := 12, gen := 10 })
      [StepCases, NF, root, try0, try1, try2, try3, lhs0, lhs1,
        lhs2, lhs3, q, sq, lhs2_not_nf,
        nodes_lt_p_left, nodes_lt_p_right]
  · rcases c3 with ⟨yo, xo, ao, bo, hto, huo, hm0o, hm1o, hm2o⟩
    grind (config := { splits := 12, gen := 10 })
      [StepCases, NF, root, try0, try1, try2, try3, lhs0, lhs1,
        lhs2, lhs3, q, sq, lhs2_not_nf,
        nodes_lt_p_left, nodes_lt_p_right]
  · rcases c4 with ⟨hto, hm0o, hm1o, hm2o, hm3o⟩
    grind (config := { splits := 12, gen := 10 })
      [StepCases, NF, root, try0, try1, try2, try3, lhs0, lhs1,
        lhs2, lhs3, q, sq, lhs2_not_nf,
        nodes_lt_p_left, nodes_lt_p_right]
theorem step_source_nf
    {x y z w yy yx zw xzw out : Raw}
    (hx : NF x) (hy : NF y) (hz : NF z) (hw : NF w)
    (hyy_nf : NF yy) (hyx_nf : NF yx)
    (hzw_nf : NF zw) (hxzw_nf : NF xzw)
    (hyy : Step (p y y) yy)
    (hyx : Step (p yy x) yx)
    (hzw : Step (p z w) zw)
    (hxzw : Step (p x zw) xzw)
    (hout : Step (p yx xzw) out) :
    out = x := by
  obtain ⟨k, hsq⟩ := step_self_square hyy
  subst yy
  exact step_source_kernel hx hyy_nf hyx_nf hzw_nf hxzw_nf
    hyx hxzw hout
theorem source_raw (x y z w : Raw)
    (hx : NF x) (hy : NF y) (hz : NF z) (hw : NF w) :
    rawOp (rawOp (rawOp y y) x) (rawOp x (rawOp z w)) = x := by
  apply step_source_nf hx hy hz hw
  · exact rawOp_nf hy hy
  · exact rawOp_nf (rawOp_nf hy hy) hx
  · exact rawOp_nf hz hw
  · exact rawOp_nf hx (rawOp_nf hz hw)
  · exact rawOp_step y y
  · exact rawOp_step (rawOp y y) x
  · exact rawOp_step z w
  · exact rawOp_step x (rawOp z w)
  · exact rawOp_step (rawOp (rawOp y y) x) (rawOp x (rawOp z w))
theorem source_holds (x y z w : Carrier) :
    x = op (op (op y y) x) (op x (op z w)) := by
  apply Subtype.ext
  exact (source_raw x.1 y.1 z.1 w.1 x.2 y.2 z.2 w.2).symm
theorem source_raw_general (x y z : Raw)
    (hx : NF x) (hy : NF y) (hz : NF z) :
    rawOp (rawOp (rawOp y y) x) (rawOp x z) = x := by
  have hyy := rawOp_step y y
  obtain ⟨k, hk⟩ := step_self_square hyy
  apply step_source_kernel (k := k) hx
  · rw [← hk]
    exact rawOp_nf hy hy
  · exact rawOp_nf (rawOp_nf hy hy) hx
  · exact hz
  · exact rawOp_nf hx hz
  · rw [← hk]
    exact rawOp_step (rawOp y y) x
  · exact rawOp_step x z
  · exact rawOp_step (rawOp (rawOp y y) x) (rawOp x z)
theorem source_holds_general (x y z : Carrier) :
    x = op (op (op y y) x) (op x z) := by
  apply Subtype.ext
  exact (source_raw_general x.1 y.1 z.1 x.2 y.2 z.2).symm
end Raw
end submission
open submission
def submission : Goal := by
  let oppositeMagma : Magma Raw.Carrier :=
    ⟨fun a b => Raw.op b a⟩
  refine ⟨Raw.Carrier, oppositeMagma, ?_, ?_⟩
  · intro _d10v0 _d10v1 _d10v2 _d10v3
    change (_d10v0) = Raw.op (Raw.op (Raw.op (_d10v3) (_d10v3)) (_d10v0)) (Raw.op (_d10v0) ((_d10v1 ◇ _d10v2)))
    exact Raw.source_holds_general (_d10v0) (_d10v3) ((_d10v1 ◇ _d10v2))
  · intro target
    first
    | have bad := target ⟨Raw.e, True.intro⟩ ⟨Raw.e, True.intro⟩ ⟨Raw.e, True.intro⟩ ⟨Raw.e, True.intro⟩
      change (Raw.op (⟨Raw.e, True.intro⟩ : Raw.Carrier) (⟨Raw.e, True.intro⟩ : Raw.Carrier)) = (Raw.op (⟨Raw.e, True.intro⟩ : Raw.Carrier) (Raw.op (Raw.op (⟨Raw.e, True.intro⟩ : Raw.Carrier) (⟨Raw.e, True.intro⟩ : Raw.Carrier)) (Raw.op (⟨Raw.e, True.intro⟩ : Raw.Carrier) (⟨Raw.e, True.intro⟩ : Raw.Carrier)))) at bad
      have badv := congrArg Subtype.val bad
      exact nomatch badv

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_23632_to_51694 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_23632_to_51694
