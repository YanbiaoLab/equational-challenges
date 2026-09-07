-- Equation13820 → Equation13557
-- Recorded verdict: false
-- Premise: x = y ◇ ((y ◇ ((x ◇ x) ◇ x)) ◇ y)
-- Conclusion: x = x ◇ ((y ◇ ((y ◇ x) ◇ y)) ◇ x)
-- Original submission SHA-256: 015a2ef2396eb43d41cfa3251a26f52925b88aad9569333d283401f370d1d5d8
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ ((y ◇ ((x ◇ x) ◇ x)) ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = x ◇ ((y ◇ ((y ◇ x) ◇ y)) ◇ x)
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Original submission body
                   

set_option maxRecDepth 10000

namespace submission

inductive CM where
  | e : CM
  | k : CM → CM
  | p : CM → CM → CM
deriving DecidableEq

namespace CM

def sz : CM → Nat
  | e => 0
  | k a => sz a + 1
  | p a b => sz a + sz b + 1

def T (a : CM) : CM := p (p a a) a
def T2 (a : CM) : CM := T (T a)
def T3 (a : CM) : CM := T (T2 a)

def R0 (a b : CM) : Prop :=
  ∃ x, b = p (p a (T x)) a

def R1 (a b : CM) : Prop :=
  ∃ x, a = T x ∧ b = p x (T x)

def R2 (a b : CM) : Prop :=
  a = T2 b

def R3 (a b : CM) : Prop :=
  ∃ x, a = T3 x ∧ b = p a a

noncomputable def op (a b : CM) : CM := by
  classical
  exact
    if h0 : R0 a b then Classical.choose h0
    else if _h1 : R1 a b then a
    else if _h2 : R2 a b then a
    else if h3 : R3 a b then Classical.choose h3
    else p a b

noncomputable instance instMagma : Magma CM where
  op := op

theorem T_inj {a b : CM} (h : T a = T b) : a = b := by
  exact (CM.p.inj h).2

theorem T2_inj {a b : CM} (h : T2 a = T2 b) : a = b :=
  T_inj (T_inj h)

theorem T3_inj {a b : CM} (h : T3 a = T3 b) : a = b :=
  T2_inj (T_inj h)

theorem op_raw {a b : CM}
    (h0 : ¬R0 a b) (h1 : ¬R1 a b)
    (h2 : ¬R2 a b) (h3 : ¬R3 a b) :
    op a b = p a b := by
  simp [op, h0, h1, h2, h3]

theorem op_r0 (a x : CM) :
    op a (p (p a (T x)) a) = x := by
  let h0 : R0 a (p (p a (T x)) a) := ⟨x, rfl⟩
  unfold op
  rw [dif_pos h0]
  have hs := Classical.choose_spec h0
  change Classical.choose h0 = x
  have ht : T (Classical.choose h0) = T x :=
    (CM.p.inj (CM.p.inj hs).1).2.symm
  exact T_inj ht

theorem not_r0_r1 (x : CM) : ¬R0 (T x) (p x (T x)) := by
  rintro ⟨z, h⟩
  have hx : x = p (T x) (T z) := (CM.p.inj h).1
  have hs := congrArg sz hx
  simp [T, sz] at hs
  omega

theorem op_r1 (x : CM) :
    op (T x) (p x (T x)) = T x := by
  have h0 := not_r0_r1 x
  have h1 : R1 (T x) (p x (T x)) := ⟨x, rfl, rfl⟩
  simp [op, h0, h1]

theorem not_r0_r2 (x : CM) : ¬R0 (T2 x) x := by
  rintro ⟨z, h⟩
  have hs := congrArg sz h
  simp [T2, T, sz] at hs
  omega

theorem not_r1_r2 (x : CM) : ¬R1 (T2 x) x := by
  rintro ⟨z, hz, hx⟩
  have hzx : T x = z := T_inj hz
  rw [← hzx] at hx
  have hs := congrArg sz hx
  simp [T, sz] at hs
  omega

theorem op_r2 (x : CM) :
    op (T2 x) x = T2 x := by
  have h0 := not_r0_r2 x
  have h1 := not_r1_r2 x
  have h2 : R2 (T2 x) x := rfl
  simp [op, h0, h1, h2]

theorem not_r0_r3 (x : CM) :
    ¬R0 (T3 x) (p (T3 x) (T3 x)) := by
  rintro ⟨z, h⟩
  have ha : T3 x = p (T3 x) (T z) := (CM.p.inj h).1
  have hs := congrArg sz ha
  simp [T3, T2, T, sz] at hs
  omega

theorem not_r1_r3 (x : CM) :
    ¬R1 (T3 x) (p (T3 x) (T3 x)) := by
  rintro ⟨z, hz, hb⟩
  have hzx : T3 x = z := (CM.p.inj hb).1
  have hcycle : T3 x = T (T3 x) := by
    calc
      T3 x = T z := hz
      _ = T (T3 x) := congrArg T hzx.symm
  have hs := congrArg sz hcycle
  simp [T3, T2, T, sz] at hs
  omega

theorem not_r2_r3 (x : CM) :
    ¬R2 (T3 x) (p (T3 x) (T3 x)) := by
  intro h
  have hs := congrArg sz h
  simp [R2, T3, T2, T, sz] at hs
  omega

theorem op_r3 (x : CM) :
    op (T3 x) (p (T3 x) (T3 x)) = x := by
  let h3 : R3 (T3 x) (p (T3 x) (T3 x)) := ⟨x, rfl, rfl⟩
  unfold op
  rw [
    dif_neg (not_r0_r3 x),
    dif_neg (not_r1_r3 x),
    dif_neg (not_r2_r3 x),
    dif_pos h3,
  ]
  have hs := Classical.choose_spec h3
  change Classical.choose h3 = x
  exact (T3_inj hs.1).symm

theorem op_diag_raw (x : CM) : op x x = p x x := by
  apply op_raw
  · rintro ⟨z, h⟩
    have hs := congrArg sz h
    simp [T, sz] at hs
    omega
  · rintro ⟨z, hz, hx⟩
    rw [hz] at hx
    have hs := congrArg sz hx
    simp [T, sz] at hs
    omega
  · intro h
    have hs := congrArg sz h
    simp [R2, T2, T, sz] at hs
    omega
  · rintro ⟨z, _, hx⟩
    have hs := congrArg sz hx
    simp [sz] at hs
    omega

theorem op_pair_raw (x : CM) : op (p x x) x = T x := by
  change op (p x x) x = p (p x x) x
  apply op_raw
  · rintro ⟨z, h⟩
    have hs := congrArg sz h
    simp [T, sz] at hs
    omega
  · rintro ⟨z, hz, hx⟩
    rw [← hz] at hx
    have hs := congrArg sz hx
    simp [T, sz] at hs
    omega
  · intro h
    have hs := congrArg sz h
    simp [R2, T2, T, sz] at hs
    omega
  · rintro ⟨z, _, hx⟩
    have hs := congrArg sz hx
    simp [sz] at hs
    omega

theorem not_r1_y_T (x y : CM) : ¬R1 y (T x) := by
  rintro ⟨z, _, h⟩
  have hz : p x x = z := (CM.p.inj h).1
  have hx : x = T z := (CM.p.inj h).2
  rw [← hz] at hx
  have hs := congrArg sz hx
  simp [T, sz] at hs
  omega

theorem not_r3_y_T (x y : CM) : ¬R3 y (T x) := by
  rintro ⟨z, _, h⟩
  have hy : p x x = y := (CM.p.inj h).1
  have hxy : x = y := (CM.p.inj h).2
  have hcycle : x = p x x := hxy.trans hy.symm
  have hs := congrArg sz hcycle
  simp [sz] at hs
  omega

theorem op_middle_raw (x y : CM)
    (h0 : ¬R0 y (T x)) (h2 : y ≠ T3 x) :
    op y (T x) = p y (T x) := by
  apply op_raw h0 (not_r1_y_T x y)
  · simpa [R2, T2, T3] using h2
  · exact not_r3_y_T x y

theorem op_middle_r2 (x y : CM)
    (h0 : ¬R0 y (T x)) (h2 : y = T3 x) :
    op y (T x) = y := by
  have hr2 : R2 y (T x) := by
    simpa [R2, T2, T3] using h2
  simp [op, h0, not_r1_y_T x y, hr2]

theorem op_nested_raw (x y : CM) :
    op (p y (T x)) y = p (p y (T x)) y := by
  apply op_raw
  · rintro ⟨z, h⟩
    have hs := congrArg sz h
    simp [T, sz] at hs
    omega
  · rintro ⟨z, hz, hy⟩
    rw [← hz] at hy
    have hs := congrArg sz hy
    simp [T, sz] at hs
    omega
  · intro h
    change p y (T x) = T2 y at h
    change p y (T x) = p (p (T y) (T y)) (T y) at h
    have hy : y = p (T y) (T y) := (CM.p.inj h).1
    have hs := congrArg sz hy
    simp [T, sz] at hs
    omega
  · rintro ⟨z, _, hy⟩
    have hs := congrArg sz hy
    simp [T, sz] at hs
    omega

theorem op_q_Tq_raw (q : CM) (hq : ¬∃ r, q = T r) :
    op q (T q) = p q (T q) := by
  apply op_raw
  · rintro ⟨z, h⟩
    have hqz : q = T z :=
      (CM.p.inj (CM.p.inj h).1).2
    exact hq ⟨z, hqz⟩
  · rintro ⟨z, hz, _⟩
    exact hq ⟨z, hz⟩
  · intro h
    have hs := congrArg sz h
    simp [R2, T2, T, sz] at hs
    omega
  · rintro ⟨z, _, hb⟩
    have hcycle : p q q = q := (CM.p.inj hb).1
    have hs := congrArg sz hcycle
    simp [sz] at hs
    omega

theorem source_holds (x y : CM) :
    x = op y (op (op y (op (op x x) x)) y) := by
  rw [op_diag_raw, op_pair_raw]
  by_cases h0 : R0 y (T x)
  · let q := Classical.choose h0
    have hq := Classical.choose_spec h0
    have hxy : x = y := (CM.p.inj hq).2
    have hxq : x = T q := (CM.p.inj (CM.p.inj hq).1).2
    have hc : op y (T x) = q := by
      unfold op
      rw [dif_pos h0]
    rw [hc]
    have hyq : y = T q := hxy.symm.trans hxq
    rw [hyq]
    by_cases hr : ∃ r, q = T r
    · let r := Classical.choose hr
      have hqr := Classical.choose_spec hr
      have hd : op q (T q) = r := by
        have ht : T q = p (p q (T r)) q :=
          congrArg (fun u => p (p q u) q) hqr
        rw [ht]
        exact op_r0 q r
      rw [hd]
      have hx2 : x = T2 r :=
        hxq.trans ((congrArg T hqr).trans rfl)
      have ht2 : T q = T2 r :=
        (congrArg T hqr).trans rfl
      rw [hx2, ht2]
      exact (op_r2 r).symm
    · rw [op_q_Tq_raw q hr]
      rw [hxq]
      exact (op_r1 q).symm
  · by_cases h2 : y = T3 x
    · rw [op_middle_r2 x y h0 h2, op_diag_raw]
      simpa [h2] using (op_r3 x).symm
    · rw [
        op_middle_raw x y h0 h2,
        op_nested_raw x y,
        op_r0 y x,
      ]

def K : CM := k e
def A : CM := p K e
def B : CM := p A K
def C : CM := p K B
def D : CM := p C e

theorem witness_A : op K e = A := by
  apply op_raw <;>
    simp [R0, R1, R2, R3, T, T2, T3, K, A]

theorem witness_B : op A K = B := by
  apply op_raw <;>
    simp [R0, R1, R2, R3, T, T2, T3, K, A, B]

theorem witness_C : op K B = C := by
  apply op_raw <;>
    simp [R0, R1, R2, R3, T, T2, T3, K, A, B, C]

theorem witness_D : op C e = D := by
  apply op_raw <;>
    simp [R0, R1, R2, R3, T, T2, T3, K, A, B, C, D]

theorem witness_rhs : op e D = p e D := by
  apply op_raw <;>
    simp [R0, R1, R2, R3, T, T2, T3, K, A, B, C, D]

end CM

end submission

open submission

noncomputable def submission : Goal := by
  refine ⟨CM, CM.instMagma, ?_, ?_⟩
  · intro x y
    change x = CM.op y
      (CM.op (CM.op y (CM.op (CM.op x x) x)) y)
    exact CM.source_holds x y
  · intro target
    have bad := target CM.e CM.K
    change CM.e = CM.op CM.e
      (CM.op (CM.op CM.K (CM.op (CM.op CM.K CM.e) CM.K)) CM.e)
      at bad
    rw [
      CM.witness_A,
      CM.witness_B,
      CM.witness_C,
      CM.witness_D,
      CM.witness_rhs,
    ] at bad
    exact CM.noConfusion bad

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_13820_to_13557 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_13820_to_13557
