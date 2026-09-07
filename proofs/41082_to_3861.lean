-- Equation41082 → Equation3861
-- Recorded verdict: false
-- Premise: x = ((((y ◇ y) ◇ z) ◇ x) ◇ x) ◇ z
-- Conclusion: x ◇ y = (z ◇ w) ◇ (u ◇ v)
-- Original submission SHA-256: 6a4571a6439514fb1a02b43b1a45f3a0c4045773f8d2492fc34bbb03b955566d
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((((y ◇ y) ◇ z) ◇ x) ◇ x) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x ◇ y = (z ◇ w) ◇ (u ◇ v)
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Original submission body
                   

set_option maxRecDepth 10000

namespace submission

inductive T where
  | g : Nat → T
  | p : T → T → T
deriving DecidableEq

namespace T

def sz : T → Nat
  | g _ => 0
  | p a b => sz a + sz b + 1

def S (a : T) : T := p a a

structure M0 (a b : T) where
  u : T
  v : T
  w : T
  ha : a = p (p (p (p u u) v) w) w
  hb : b = v

structure M1 (a b : T) where
  u : T
  ha : a = S u
  hb : b = S u

structure M2 (a b : T) where
  u : T
  v : T
  ha : a = p (p (p u u) v) v
  hb : b = p (p u u) v

structure M3 (a b : T) where
  u : T
  v : T
  ha : a = p (p (p u u) v) v
  hb : b = p u u
  guard : p u u ≠ v

def R0 (a b : T) : Prop := Nonempty (M0 a b)
def R1 (a b : T) : Prop := Nonempty (M1 a b)
def R2 (a b : T) : Prop := Nonempty (M2 a b)
def R3 (a b : T) : Prop := Nonempty (M3 a b)

def NF : T → Prop
  | g _ => True
  | p a b =>
      NF a ∧ NF b ∧ ¬R0 a b ∧ ¬R1 a b ∧ ¬R2 a b ∧ ¬R3 a b

abbrev CM := {a : T // NF a}

theorem nf_l {a b : T} (h : NF (p a b)) : NF a := h.1
theorem nf_r {a b : T} (h : NF (p a b)) : NF b := h.2.1

theorem m0_nf {a b : T} (ha : NF a) (m : M0 a b) : NF m.w := by
  rw [m.ha] at ha
  exact nf_r ha

theorem m2_nf {a b : T} (ha : NF a) (m : M2 a b) : NF m.v := by
  rw [m.ha] at ha
  exact nf_r ha

theorem m3_nf {a b : T} (ha : NF a) (m : M3 a b) : NF m.v := by
  rw [m.ha] at ha
  exact nf_r ha

noncomputable def op (a b : CM) : CM := by
  classical
  exact
    if h0 : R0 a.1 b.1 then
      let m := Classical.choice h0
      ⟨m.w, m0_nf a.2 m⟩
    else if _h1 : R1 a.1 b.1 then a
    else if h2 : R2 a.1 b.1 then
      let m := Classical.choice h2
      ⟨m.v, m2_nf a.2 m⟩
    else if h3 : R3 a.1 b.1 then
      let m := Classical.choice h3
      ⟨m.v, m3_nf a.2 m⟩
    else
      ⟨p a.1 b.1, a.2, b.2, h0, _h1, h2, h3⟩

noncomputable instance instMagma : Magma CM where
  op := op

theorem m0_w_unique {a b : T} (m n : M0 a b) : m.w = n.w :=
  (T.p.inj (m.ha.symm.trans n.ha)).2

theorem m2_v_unique {a b : T} (m n : M2 a b) : m.v = n.v :=
  (T.p.inj (m.ha.symm.trans n.ha)).2

theorem m3_v_unique {a b : T} (m n : M3 a b) : m.v = n.v :=
  (T.p.inj (m.ha.symm.trans n.ha)).2

theorem op_r0 {a b : CM} (m : M0 a.1 b.1) (c : CM)
    (hc : m.w = c.1) : op a b = c := by
  apply Subtype.ext
  simp only [op, dif_pos (show R0 a.1 b.1 from ⟨m⟩)]
  exact (m0_w_unique (Classical.choice (show R0 a.1 b.1 from ⟨m⟩)) m).trans hc

theorem op_r1 {a b : CM} (h0 : ¬R0 a.1 b.1) (m : M1 a.1 b.1) :
    op a b = a := by
  simp [op, h0, show R1 a.1 b.1 from ⟨m⟩]

theorem op_r2 {a b : CM} (h0 : ¬R0 a.1 b.1)
    (h1 : ¬R1 a.1 b.1) (m : M2 a.1 b.1) (c : CM)
    (hc : m.v = c.1) : op a b = c := by
  apply Subtype.ext
  simp only [op, dif_neg h0, dif_neg h1,
    dif_pos (show R2 a.1 b.1 from ⟨m⟩)]
  exact (m2_v_unique (Classical.choice (show R2 a.1 b.1 from ⟨m⟩)) m).trans hc

theorem op_r3 {a b : CM} (h0 : ¬R0 a.1 b.1)
    (h1 : ¬R1 a.1 b.1) (h2 : ¬R2 a.1 b.1)
    (m : M3 a.1 b.1) (c : CM) (hc : m.v = c.1) :
    op a b = c := by
  apply Subtype.ext
  simp only [op, dif_neg h0, dif_neg h1, dif_neg h2,
    dif_pos (show R3 a.1 b.1 from ⟨m⟩)]
  exact (m3_v_unique (Classical.choice (show R3 a.1 b.1 from ⟨m⟩)) m).trans hc

theorem op_raw {a b : CM}
    (h0 : ¬R0 a.1 b.1) (h1 : ¬R1 a.1 b.1)
    (h2 : ¬R2 a.1 b.1) (h3 : ¬R3 a.1 b.1) :
    (op a b).1 = p a.1 b.1 := by
  simp [op, h0, h1, h2, h3]

theorem no_r0_diag (a : T) : ¬R0 a a := by
  rintro ⟨m⟩
  have h : m.v = p (p (p (p m.u m.u) m.v) m.w) m.w :=
    m.hb.symm.trans m.ha
  have hs := congrArg sz h
  simp [sz] at hs
  omega

theorem no_r2_diag (a : T) : ¬R2 a a := by
  rintro ⟨m⟩
  have h := m.hb.symm.trans m.ha
  have hs := congrArg sz h
  simp [sz] at hs
  omega

theorem no_r3_diag (a : T) : ¬R3 a a := by
  rintro ⟨m⟩
  have h := m.hb.symm.trans m.ha
  have hs := congrArg sz h
  simp [sz] at hs
  omega

theorem diag_shape (y : CM) : ∃ a, (op y y).1 = S a := by
  by_cases h : ∃ a, y.1 = S a
  · obtain ⟨a, ha⟩ := h
    have m : M1 y.1 y.1 := ⟨a, ha, ha⟩
    rw [op_r1 (no_r0_diag y.1) m]
    exact ⟨a, ha⟩
  · have h1 : ¬R1 y.1 y.1 := by
      rintro ⟨m⟩
      exact h ⟨m.u, m.ha⟩
    rw [op_raw (no_r0_diag y.1) h1 (no_r2_diag y.1) (no_r3_diag y.1)]
    exact ⟨y.1, rfl⟩

theorem square_child_not_square (q : CM) {a : T} (hq : q.1 = S a) :
    ¬ ∃ u, a = S u := by
  rintro ⟨u, hu⟩
  have hn := q.2
  rw [hq, hu] at hn
  exact hn.2.2.2.1 ⟨⟨u, rfl, rfl⟩⟩

theorem square_r0_none (q z : CM) {a : T} (hq : q.1 = S a) :
    ¬R0 q.1 z.1 := by
  rintro ⟨m⟩
  have h := hq.symm.trans m.ha
  have h1 := T.p.inj h
  have ha := h1.1
  rw [← h1.2] at ha
  have hs := congrArg sz ha
  simp [sz] at hs
  omega

theorem square_r2_none (q z : CM) {a : T} (hq : q.1 = S a) :
    ¬R2 q.1 z.1 := by
  rintro ⟨m⟩
  have h := hq.symm.trans m.ha
  have hi := T.p.inj h
  have ha := hi.1
  have hv := hi.2
  rw [← hv] at ha
  have hs := congrArg sz ha
  simp [sz] at hs
  omega

theorem square_r3_none (q z : CM) {a : T} (hq : q.1 = S a) :
    ¬R3 q.1 z.1 := by
  rintro ⟨m⟩
  have h := hq.symm.trans m.ha
  have hi := T.p.inj h
  have ha := hi.1
  have hv := hi.2
  rw [← hv] at ha
  have hs := congrArg sz ha
  simp [sz] at hs
  omega

theorem square_mul_self (q : CM) {a : T} (hq : q.1 = S a) :
    op q q = q := by
  apply op_r1 (square_r0_none q q hq)
  exact ⟨a, hq, hq⟩

theorem square_mul_other (q z : CM) {a : T} (hq : q.1 = S a)
    (hz : Not (z = q)) : (op q z).1 = p q.1 z.1 := by
  apply op_raw (square_r0_none q z hq)
  · rintro ⟨m⟩
    have : z.1 = q.1 := m.hb.trans m.ha.symm
    exact hz (Subtype.ext this)
  · exact square_r2_none q z hq
  · exact square_r3_none q z hq

-- The remaining source proof follows the four frozen branches in DESIGN.md.
-- Each helper below states one complete root-classification fact.

theorem zq_second_raw (q x : CM) {a : T} (hq : q.1 = S a)
    (hx : x ≠ q) :
    (op (op q x) x).1 = p (p q.1 x.1) x.1 := by
  have hu := square_mul_other q x hq hx
  have h0 : ¬R0 (op q x).1 x.1 := by
    rintro ⟨m⟩
    have mha := hu.symm.trans m.ha
    have hi := T.p.inj mha
    have hh := T.p.inj (hq.symm.trans hi.1)
    have hax : a = x.1 := hh.2.trans hi.2.symm
    have hcycle := hh.1
    rw [hax, ← m.hb] at hcycle
    have hs := congrArg sz hcycle
    simp [S, sz] at hs
    omega
  have h1 : ¬R1 (op q x).1 x.1 := by
    rintro ⟨m⟩
    have hcycle : p q.1 x.1 = x.1 := hu.symm.trans (m.ha.trans m.hb.symm)
    have hs := congrArg sz hcycle
    simp [sz] at hs
    omega
  have h2 : ¬R2 (op q x).1 x.1 := by
    rintro ⟨m⟩
    have mha := hu.symm.trans m.ha
    have hi := T.p.inj mha
    have hqx : q.1 = x.1 := hi.1.trans m.hb.symm
    exact hx (Subtype.ext hqx.symm)
  have h3 : ¬R3 (op q x).1 x.1 := by
    rintro ⟨m⟩
    have mha := hu.symm.trans m.ha
    have hi := T.p.inj mha
    exact m.guard (m.hb.symm.trans hi.2)
  rw [op_raw h0 h1 h2 h3, hu]

theorem zq_finish (q x : CM) {a : T} (hq : q.1 = S a)
    (hx : x ≠ q) :
    op (op (op q x) x) q = x := by
  let u := op q x
  let v := op u x
  have hu : u.1 = p q.1 x.1 := square_mul_other q x hq hx
  have hv : v.1 = p (p q.1 x.1) x.1 := zq_second_raw q x hq hx
  have h0 : ¬R0 v.1 q.1 := by
    rintro ⟨m⟩
    have mha := hv.symm.trans m.ha
    have hi := T.p.inj mha
    have hi2 := T.p.inj hi.1
    have hcycle := hi2.1
    rw [← m.hb] at hcycle
    have hs := congrArg sz hcycle
    simp [sz] at hs
    omega
  have h1 : ¬R1 v.1 q.1 := by
    rintro ⟨m⟩
    have hcycle : p (p q.1 x.1) x.1 = q.1 :=
      hv.symm.trans (m.ha.trans m.hb.symm)
    have hs := congrArg sz hcycle
    simp [sz] at hs
    omega
  have h2 : ¬R2 v.1 q.1 := by
    rintro ⟨m⟩
    have mha := hv.symm.trans m.ha
    have hi := T.p.inj mha
    have hi2 := T.p.inj hi.1
    have hcycle := m.hb
    rw [← hi2.1, ← hi.2] at hcycle
    have hs := congrArg sz hcycle
    simp [sz] at hs
    omega
  have guard : p a a ≠ x.1 := by
    intro h
    exact hx (Subtype.ext (h.symm.trans hq.symm))
  have hq' : q.1 = p a a := by simpa only [S] using hq
  have mha : v.1 = p (p (p a a) x.1) x.1 := by
    rw [hv, hq']
  let m : M3 v.1 q.1 := ⟨a, x.1, mha, hq', guard⟩
  exact op_r3 h0 h1 h2 m x rfl

def Collision (q z x : CM) : Prop :=
  ∃ u, q.1 = S z.1 ∧ z.1 = p (S u) x.1

theorem second_collision (q z x : CM) {a : T} (hq : q.1 = S a)
    (hz : z ≠ q) (hc : Collision q z x) :
    op (op q z) x = z := by
  obtain ⟨u, hqz, hzx⟩ := hc
  have ht := square_mul_other q z hq hz
  have hqz' : q.1 = p z.1 z.1 := by simpa only [S] using hqz
  have hzx' : z.1 = p (p u u) x.1 := by simpa only [S] using hzx
  have mha :
      (op q z).1 = p (p (p (p u u) x.1) z.1) z.1 := by
    rw [ht, hqz', hzx']
  let m : M0 (op q z).1 x.1 := ⟨u, x.1, z.1, mha, rfl⟩
  exact op_r0 m z rfl

theorem second_noncollision (q z x : CM) {a : T} (hq : q.1 = S a)
    (hz : z ≠ q) (hc : ¬Collision q z x) :
    (op (op q z) x).1 = p (p q.1 z.1) x.1 := by
  have ht := square_mul_other q z hq hz
  have h0 : ¬R0 (op q z).1 x.1 := by
    rintro ⟨m⟩
    have mha := ht.symm.trans m.ha
    have hi := T.p.inj mha
    have hs := T.p.inj (hq.symm.trans hi.1)
    have haz : a = z.1 := hs.2.trans hi.2.symm
    apply hc
    refine ⟨m.u, ?_, ?_⟩
    · exact hq.trans (congrArg S haz)
    · calc
        z.1 = a := haz.symm
        _ = p (p m.u m.u) m.v := hs.1
        _ = p (p m.u m.u) x.1 := by rw [← m.hb]
        _ = p (S m.u) x.1 := rfl
  have h1 : ¬R1 (op q z).1 x.1 := by
    rintro ⟨m⟩
    have hp : p q.1 z.1 = S m.u := ht.symm.trans m.ha
    have hi := T.p.inj hp
    exact hz (Subtype.ext (hi.1.trans hi.2.symm).symm)
  have h2 : ¬R2 (op q z).1 x.1 := by
    rintro ⟨m⟩
    have mha := ht.symm.trans m.ha
    have hi := T.p.inj mha
    have hs := T.p.inj (hq.symm.trans hi.1)
    exact square_child_not_square q hq ⟨m.u, hs.1⟩
  have h3 : ¬R3 (op q z).1 x.1 := by
    rintro ⟨m⟩
    have mha := ht.symm.trans m.ha
    have hi := T.p.inj mha
    have hs := T.p.inj (hq.symm.trans hi.1)
    exact m.guard (hs.1.symm.trans hs.2)
  rw [op_raw h0 h1 h2 h3, ht]

theorem collision_finish (q z x : CM) {a : T} (hq : q.1 = S a)
    (hz : z ≠ q) (hc : Collision q z x) :
    op (op (op (op q z) x) x) z = x := by
  obtain ⟨u, hqz, hzx⟩ := hc
  rw [second_collision q z x hq hz ⟨u, hqz, hzx⟩]
  have haz : a = z.1 := T.p.inj (hq.symm.trans hqz) |>.1
  have h0m : ¬R0 z.1 x.1 := by
    rintro ⟨m⟩
    have mha := hzx.symm.trans m.ha
    have hi := T.p.inj mha
    have hi2 := T.p.inj hi.1
    have hcycle := hi2.1
    have hux : u = x.1 := hi2.2.trans hi.2.symm
    rw [hux, ← m.hb] at hcycle
    have hs := congrArg sz hcycle
    simp [sz] at hs
    omega
  have h1m : ¬R1 z.1 x.1 := by
    rintro ⟨m⟩
    have hcycle : p (S u) x.1 = x.1 := hzx.symm.trans (m.ha.trans m.hb.symm)
    have hs := congrArg sz hcycle
    simp [sz] at hs
    omega
  have h2m : ¬R2 z.1 x.1 := by
    rintro ⟨m⟩
    have mha := hzx.symm.trans m.ha
    have hi := T.p.inj mha
    have hsx : S u = x.1 := hi.1.trans m.hb.symm
    apply square_child_not_square q hq
    refine ⟨x.1, ?_⟩
    calc
      a = z.1 := haz
      _ = p (S u) x.1 := hzx
      _ = p x.1 x.1 := by rw [hsx]
      _ = S x.1 := rfl
  have h3m : ¬R3 z.1 x.1 := by
    rintro ⟨m⟩
    have mha := hzx.symm.trans m.ha
    have hi := T.p.inj mha
    exact m.guard (m.hb.symm.trans hi.2)
  have hm : (op z x).1 = p z.1 x.1 := op_raw h0m h1m h2m h3m
  have h0 : ¬R0 (op z x).1 z.1 := by
    rintro ⟨m⟩
    have mha := hm.symm.trans m.ha
    have hi := T.p.inj mha
    have hz' := hzx.symm.trans hi.1
    have hi2 := T.p.inj hz'
    have hi3 := T.p.inj hi2.1
    have huz : u = z.1 := hi3.2.trans m.hb.symm
    have hcycle := hzx
    rw [huz] at hcycle
    have hs := congrArg sz hcycle
    simp [S, sz] at hs
    omega
  have h1 : ¬R1 (op z x).1 z.1 := by
    rintro ⟨m⟩
    have hcycle : p z.1 x.1 = z.1 := hm.symm.trans (m.ha.trans m.hb.symm)
    have hs := congrArg sz hcycle
    simp [sz] at hs
    omega
  have hzx' : z.1 = p (p u u) x.1 := by simpa only [S] using hzx
  have mha : (op z x).1 = p (p (p u u) x.1) x.1 := by
    rw [hm, hzx']
  let m : M2 (op z x).1 z.1 := ⟨u, x.1, mha, hzx'⟩
  exact op_r2 h0 h1 m x rfl

theorem noncollision_finish (q z x : CM) {a : T} (hq : q.1 = S a)
    (hz : z ≠ q) (hc : ¬Collision q z x) :
    op (op (op (op q z) x) x) z = x := by
  let r := op (op q z) x
  have hr : r.1 = p (p q.1 z.1) x.1 :=
    second_noncollision q z x hq hz hc
  have h0 : ¬R0 r.1 x.1 := by
    rintro ⟨m⟩
    have mha := hr.symm.trans m.ha
    have hi := T.p.inj mha
    have hi2 := T.p.inj hi.1
    have hs := T.p.inj (hq.symm.trans hi2.1)
    exact square_child_not_square q hq ⟨m.u, hs.1⟩
  have h1 : ¬R1 r.1 x.1 := by
    rintro ⟨m⟩
    have hcycle : p (p q.1 z.1) x.1 = x.1 :=
      hr.symm.trans (m.ha.trans m.hb.symm)
    have hs := congrArg sz hcycle
    simp [sz] at hs
    omega
  have h2 : ¬R2 r.1 x.1 := by
    rintro ⟨m⟩
    have mha := hr.symm.trans m.ha
    have hi := T.p.inj mha
    have hi2 := T.p.inj hi.1
    have hcycle := m.hb
    rw [← hi2.1, ← hi.2] at hcycle
    have hs := congrArg sz hcycle
    simp [sz] at hs
    omega
  have h3 : ¬R3 r.1 x.1 := by
    rintro ⟨m⟩
    have mha := hr.symm.trans m.ha
    have hi := T.p.inj mha
    exact m.guard (m.hb.symm.trans hi.2)
  have hv : (op r x).1 = p (p (p q.1 z.1) x.1) x.1 := by
    rw [op_raw h0 h1 h2 h3, hr]
  have hq' : q.1 = p a a := by simpa only [S] using hq
  have mha :
      (op r x).1 = p (p (p (p a a) z.1) x.1) x.1 := by
    rw [hv, hq']
  let m : M0 (op r x).1 z.1 := ⟨a, z.1, x.1, mha, rfl⟩
  exact op_r0 m x rfl

theorem source_holds (x y z : CM) :
    op (op (op (op (op y y) z) x) x) z = x := by
  let q := op y y
  obtain ⟨a, hq⟩ := diag_shape y
  change (q.1 = S a) at hq
  change op (op (op (op q z) x) x) z = x
  by_cases hz : z = q
  · subst z
    by_cases hx : x = q
    · subst x
      rw [square_mul_self q hq, square_mul_self q hq,
        square_mul_self q hq, square_mul_self q hq]
    · rw [square_mul_self q hq]
      exact zq_finish q x hq hx
  · by_cases hc : Collision q z x
    · exact collision_finish q z x hq hz hc
    · exact noncollision_finish q z x hq hz hc

def IsGenerator : T → Prop
  | .g _ => True
  | .p _ _ => False

def gx : CM := ⟨g 0, trivial⟩
def gy : CM := ⟨g 1, trivial⟩
def gz : CM := ⟨g 2, trivial⟩
def gw : CM := ⟨g 3, trivial⟩

theorem atom_left_raw (i : Nat) (b : CM) :
    (op (⟨g i, trivial⟩ : CM) b).1 = p (g i) b.1 := by
  apply op_raw
  · rintro ⟨m⟩
    cases m.ha
  · rintro ⟨m⟩
    cases m.ha
  · rintro ⟨m⟩
    cases m.ha
  · rintro ⟨m⟩
    cases m.ha

theorem target_mid_raw (a : CM)
    (ha : a.1 = p (g 1) (p (g 2) (g 0))) :
    (op a gw).1 = p a.1 (g 3) := by
  apply op_raw
  · rintro ⟨m⟩
    have mha := ha.symm.trans m.ha
    cases (T.p.inj mha).1
  · rintro ⟨m⟩
    have mha := ha.symm.trans m.ha
    have hi := T.p.inj mha
    cases hi.1.trans hi.2.symm
  · rintro ⟨m⟩
    have mha := ha.symm.trans m.ha
    cases (T.p.inj mha).1
  · rintro ⟨m⟩
    have mha := ha.symm.trans m.ha
    cases (T.p.inj mha).1

theorem target_last_raw (a : CM)
    (ha : a.1 = p (p (g 1) (p (g 2) (g 0))) (g 3)) :
    (op a gx).1 = p a.1 (g 0) := by
  apply op_raw
  · rintro ⟨m⟩
    have mha := ha.symm.trans m.ha
    have hi := T.p.inj mha
    cases (T.p.inj hi.1).1
  · rintro ⟨m⟩
    have mha := ha.symm.trans m.ha
    have hi := T.p.inj mha
    cases hi.1.trans hi.2.symm
  · rintro ⟨m⟩
    have mha := ha.symm.trans m.ha
    have hi := T.p.inj mha
    cases (T.p.inj hi.1).1
  · rintro ⟨m⟩
    have mha := ha.symm.trans m.ha
    have hi := T.p.inj mha
    cases (T.p.inj hi.1).1

theorem target_fails :
    ¬∀ x y z w : CM, op x y = op (op (op y (op z x)) w) x := by
  intro h
  let zx := op gz gx
  let yzx := op gy zx
  let mid := op yzx gw
  have hl : (op gx gy).1 = p (g 0) (g 1) := by
    simpa [gx, gy] using atom_left_raw 0 gy
  have hzx : zx.1 = p (g 2) (g 0) := by
    simpa [zx, gz, gx] using atom_left_raw 2 gx
  have hyzx : yzx.1 = p (g 1) (p (g 2) (g 0)) := by
    change (op gy zx).1 = _
    rw [show (op gy zx).1 = p (g 1) zx.1 by
      simpa [gy] using atom_left_raw 1 zx, hzx]
  have hmid : mid.1 = p (p (g 1) (p (g 2) (g 0))) (g 3) := by
    change (op yzx gw).1 = _
    rw [target_mid_raw yzx hyzx, hyzx]
  have hr :
      (op mid gx).1 =
        p (p (p (g 1) (p (g 2) (g 0))) (g 3)) (g 0) := by
    rw [target_last_raw mid hmid, hmid]
  have bad := congrArg Subtype.val (h gx gy gz gw)
  change (op gx gy).1 = (op mid gx).1 at bad
  rw [hl, hr] at bad
  cases (T.p.inj bad).1

end T
end submission

open submission

noncomputable def submission : Goal := by
  refine ⟨T.CM, T.instMagma, ?_, ?_⟩
  · intro x y z
    exact (T.source_holds x y z).symm
  · intro target
    have hxx :
        (T.op T.gx T.gx).1 = T.p (T.g 0) (T.g 0) := by
      simpa [T.gx] using T.atom_left_raw 0 T.gx
    have hxy :
        (T.op T.gx T.gy).1 = T.p (T.g 0) (T.g 1) := by
      simpa [T.gx, T.gy] using T.atom_left_raw 0 T.gy
    have hsquare :
        (T.op T.gx T.gx).1 = T.S (T.g 0) := by
      simpa [T.S] using hxx
    have hne : Not (T.op T.gx T.gy = T.op T.gx T.gx) := by
      intro h
      have hv := congrArg Subtype.val h
      rw [hxy, hxx] at hv
      have hbad : T.g 1 = T.g 0 := (T.p.inj hv).2
      have hnat : (1 : Nat) = 0 := T.g.inj hbad
      exact (by decide : Not ((1 : Nat) = 0)) hnat
    have houter :=
      T.square_mul_other
        (T.op T.gx T.gx) (T.op T.gx T.gy) hsquare hne
    have bad := congrArg Subtype.val
      (target T.gx T.gx T.gx T.gx T.gx T.gy)
    change
      (T.op T.gx T.gx).1 =
        (T.op (T.op T.gx T.gx) (T.op T.gx T.gy)).1 at bad
    rw [hxx, houter, hxx, hxy] at bad
    have hbad : T.g 0 = T.p (T.g 0) (T.g 0) := (T.p.inj bad).1
    have htag : T.IsGenerator (T.g 0) =
        T.IsGenerator (T.p (T.g 0) (T.g 0)) :=
      congrArg T.IsGenerator hbad
    exact Eq.mp htag True.intro

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_41082_to_3861 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_41082_to_3861
