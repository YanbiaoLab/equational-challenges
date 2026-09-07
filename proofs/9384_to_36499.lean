-- Equation9384 → Equation36499
-- Recorded verdict: false
-- Premise: x = y * ((x * z) * (y * (z * z)))
-- Conclusion: x = (((y * x) * x) * (z * z)) * y
-- Original submission SHA-256: ef43b5d3e945d1ba0fc7af9531eaa2c6bb655d41f5def9a04eecb3cca008015c
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ ((x ◇ z) ◇ (y ◇ (z ◇ z)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (((y ◇ x) ◇ x) ◇ (z ◇ z)) ◇ y
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

def S (q : T) : T := p q q

def D (a b c : T) : T :=
  p (p b c) (p a (S c))

def W (r a q : T) : T :=
  p r (p a (S q))

inductive ST : T → T → Prop
  | left (a b : T) : ST a (p a b)
  | right (a b : T) : ST b (p a b)
  | trans {a b c : T} : ST a b → ST b c → ST a c

def ST.upL {x a : T} (h : ST x a) (b : T) : ST x (p a b) :=
  ST.trans h (ST.left a b)

def ST.upR (a : T) {x b : T} (h : ST x b) : ST x (p a b) :=
  ST.trans h (ST.right a b)

theorem st_sz {a b : T} (h : ST a b) : sz a < sz b := by
  induction h with
  | left a b => simp [sz] <;> omega
  | right a b => simp [sz] <;> omega
  | trans _ _ ih₁ ih₂ => omega

/- `Code q a r` is the shared decoder graph: using `a` as the left
   operand and `q` as the right operand returns `r`.  The same graph read
   backwards is the frozen preimage relation. -/
inductive Code : T → T → T → Prop
  | base (a b c : T) : Code (D a b c) a b
  | succ {q c r : T} (h : Code q c r) (a : T) :
      Code (W r a q) a c

theorem code_input_st {q a r : T} (h : Code q a r) : ST a q := by
  cases h with
  | base a b c =>
      exact ST.upR _ (ST.left a (S c))
  | @succ q c r h a =>
      exact ST.upR r (ST.left a (S q))

theorem code_output_st {q a r : T} (h : Code q a r) : ST r q := by
  induction h with
  | base a b c =>
      exact ST.upL (ST.left b c) (p a (S c))
  | @succ q c r h a ih =>
      exact ST.upR r
        (ST.upR a (ST.upL (code_input_st h) q))

theorem code_input_small {q a r : T} (h : Code q a r) :
    sz a < sz q :=
  st_sz (code_input_st h)

theorem code_output_small {q a r : T} (h : Code q a r) :
    sz r < sz q :=
  st_sz (code_output_st h)

theorem base_succ_ne {a b c q u r v : T}
    (h : Code q u r) : D a b c ≠ W r v q := by
  intro he
  unfold D W S at he
  injection he with hl hr
  injection hr with _ hs
  injection hs with hc _
  have hout := code_output_small h
  rw [← hc, ← hl] at hout
  simp [sz] at hout <;> omega

theorem code_left_unique
    {q₁ q₂ a₁ a₂ r₁ r₂ : T}
    (h₁ : Code q₁ a₁ r₁) (h₂ : Code q₂ a₂ r₂)
    (hq : q₁ = q₂) (hr : r₁ = r₂) : a₁ = a₂ := by
  cases h₁ with
  | base a b c =>
      cases h₂ with
      | base u v w =>
          unfold D at hq
          exact (p.inj (p.inj hq).2).1
      | @succ q u r h v =>
          exact (base_succ_ne h hq).elim
  | @succ q c r h a =>
      cases h₂ with
      | base u v w =>
          exact (base_succ_ne h hq.symm).elim
      | @succ q₂ c₂ r₂ h₂ a₂ =>
          unfold W at hq
          exact (p.inj (p.inj hq).2).1

theorem code_right_unique
    {q₁ q₂ a₁ a₂ r₁ r₂ : T}
    (h₁ : Code q₁ a₁ r₁) (h₂ : Code q₂ a₂ r₂)
    (hq : q₁ = q₂) (ha : a₁ = a₂) : r₁ = r₂ := by
  cases h₁ with
  | base a b c =>
      cases h₂ with
      | base u v w =>
          unfold D at hq
          exact (p.inj (p.inj hq).1).1
      | @succ q u r h v =>
          exact (base_succ_ne h hq).elim
  | @succ q c r h a =>
      cases h₂ with
      | base u v w =>
          exact (base_succ_ne h hq.symm).elim
      | @succ q₂ c₂ r₂ h₂ a₂ =>
          unfold W S at hq
          have outer := p.inj hq
          have inner := p.inj outer.2
          have square := p.inj inner.2
          exact code_left_unique h h₂ square.1 outer.1

noncomputable def eval (a q : T) : T := by
  classical
  exact if h : ∃ r, Code q a r then Classical.choose h else p a q

theorem eval_hit {q a r : T} (h : Code q a r) :
    eval a q = r := by
  rw [eval, dif_pos ⟨r, h⟩]
  exact code_right_unique (Classical.choose_spec ⟨r, h⟩) h rfl rfl

theorem eval_raw {q a : T} (h : ¬ ∃ r, Code q a r) :
    eval a q = p a q := by
  simp [eval, h]

theorem no_code_self (q : T) : ¬ ∃ r, Code q q r := by
  rintro ⟨r, h⟩
  have hs := code_input_small h
  omega

theorem D_not_square (a b c z : T) :
    D a b c ≠ S z := by
  intro hq
  unfold D S at hq
  have outer := p.inj hq
  have he : p b c = p a (p c c) := outer.1.trans outer.2.symm
  have hc := (p.inj he).2
  have hs := congrArg sz hc
  simp [sz] at hs <;> omega

theorem code_not_square {q a r z : T}
    (h : Code q a r) (hq : q = S z) : False := by
  cases h with
  | base u v c =>
      exact D_not_square _ _ _ _ hq
  | @succ q c r h u =>
      unfold W S at hq
      have outer := p.inj hq
      have hout := code_output_small h
      have hqz : sz q < sz z := by
        rw [← outer.2]
        simp [S, sz] <;> omega
      rw [outer.1] at hout
      omega

theorem no_code_square (a z : T) :
    ¬ ∃ r, Code (S z) a r := by
  rintro ⟨r, h⟩
  exact code_not_square h rfl

theorem code_join_input {q a r y z : T}
    (h : Code q a r) (hq : q = p y (S z)) : a = z := by
  cases h with
  | base u v c =>
      unfold D S at hq
      exact (p.inj (p.inj hq).2).1
  | @succ q c r h u =>
      unfold W S at hq
      exact (p.inj (p.inj hq).2).1

theorem no_code_after_hit {x z r y : T} (h : Code z x r) :
    ¬ ∃ s, Code (p y (S z)) r s := by
  rintro ⟨s, k⟩
  have hrz := code_join_input k rfl
  have hs := code_output_small h
  rw [hrz] at hs
  omega

theorem no_code_after_raw (x z y : T) :
    ¬ ∃ s, Code (p y (S z)) (p x z) s := by
  rintro ⟨s, k⟩
  have he := code_join_input k rfl
  have hs := congrArg sz he
  simp [sz] at hs <;> omega

theorem source_eval (x y z : T) :
    eval y (eval (eval x z) (eval y (eval z z))) = x := by
  rw [eval_raw (no_code_self z)]
  rw [show eval y (p z z) = p y (p z z) by
    simpa [S] using eval_raw (no_code_square y z)]
  by_cases hx : ∃ r, Code z x r
  · let r := Classical.choose hx
    have hr : Code z x r := Classical.choose_spec hx
    rw [eval_hit hr]
    rw [show eval r (p y (p z z)) = p r (p y (p z z)) by
      simpa [S] using eval_raw (no_code_after_hit hr)]
    simpa [W, S] using eval_hit (Code.succ hr y)
  · rw [eval_raw hx]
    rw [show eval (p x z) (p y (p z z)) =
        p (p x z) (p y (p z z)) by
      simpa [S] using eval_raw (no_code_after_raw x z y)]
    simpa [D, S] using eval_hit (Code.base y x z)

theorem code_min_size {q a r : T} (h : Code q a r) :
    3 ≤ sz q := by
  cases h with
  | base a b c =>
      simp [D, S, sz] <;> omega
  | @succ q c r h a =>
      simp [W, S, sz] <;> omega

theorem no_code_small {q a : T} (hq : sz q < 3) :
    ¬ ∃ r, Code q a r := by
  rintro ⟨r, h⟩
  have hs := code_min_size h
  omega

theorem eval_atom (a : T) (n : Nat) :
    eval a (g n) = p a (g n) :=
  eval_raw (no_code_small (by simp [sz]))

theorem eval_atom_pair (a : T) (m n : Nat) :
    eval a (p (g m) (g n)) = p a (p (g m) (g n)) :=
  eval_raw (no_code_small (by simp [sz]))

noncomputable instance instMagma : Magma T where
  op := eval

theorem source_holds (x y z : T) :
    x = y ◇ ((x ◇ z) ◇ (y ◇ (z ◇ z))) := by
  change x = eval y (eval (eval x z) (eval y (eval z z)))
  exact (source_eval x y z).symm

def gx : T := g 0
def gy : T := g 1
def gz : T := g 2
def gw : T := g 3

theorem target27802_value :
    ((gy ◇ (gx ◇ gz)) ◇ gy) ◇ (gz ◇ gw) =
      p (p (p gy (p gx gz)) gy) (p gz gw) := by
  change
    eval (eval (eval gy (eval gx gz)) gy) (eval gz gw) =
      p (p (p gy (p gx gz)) gy) (p gz gw)
  simp [gx, gy, gz, gw, eval_atom, eval_atom_pair]

theorem bad27802 :
    gx ≠ ((gy ◇ (gx ◇ gz)) ◇ gy) ◇ (gz ◇ gw) := by
  rw [target27802_value]
  intro h
  cases h

theorem target36499_value :
    (((gy ◇ gx) ◇ gx) ◇ (gz ◇ gz)) ◇ gy =
      p (p (p (p gy gx) gx) (p gz gz)) gy := by
  change
    eval (eval (eval (eval gy gx) gx) (eval gz gz)) gy =
      p (p (p (p gy gx) gx) (p gz gz)) gy
  simp [gx, gy, gz, eval_atom, eval_atom_pair]

theorem bad36499 :
    gx ≠ (((gy ◇ gx) ◇ gx) ◇ (gz ◇ gz)) ◇ gy := by
  rw [target36499_value]
  intro h
  cases h

end T
end submission


open submission

noncomputable def submission : Goal := by
  refine ⟨T, T.instMagma, ?_, ?_⟩
  · intro x y z
    exact T.source_holds x y z
  · intro target
    exact T.bad36499 (target T.gx T.gy T.gz)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_9384_to_36499 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_9384_to_36499
