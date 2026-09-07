-- Equation9384 → Equation9
-- Recorded verdict: false
-- Premise: x = y ◇ ((x ◇ z) ◇ (y ◇ (z ◇ z)))
-- Conclusion: x = x ◇ (x ◇ y)
-- Original submission SHA-256: 64d505b1f6eb93bdb8febe3450b913b1d2be3e2c855c46588fa8c54f94133a95
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
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = x ◇ (x ◇ y)
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Original submission body
-- stage:stage0_generalized_infinite_source_family
                   

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

def baseForward (q a : T) : Option T :=
  match q with
  | p (p b c) (p a' (p c' c'')) =>
      if ha : a' = a then
        if hc1 : c' = c then
          if hc2 : c'' = c then by
            subst a'; subst c'; subst c''
            exact some b
          else none
        else none
      else none
  | _ => none

def baseBackward (q r : T) : Option T :=
  match q with
  | p (p b c) (p a (p c' c'')) =>
      if hb : b = r then
        if hc1 : c' = c then
          if hc2 : c'' = c then by
            subst b; subst c'; subst c''
            exact some a
          else none
        else none
      else none
  | _ => none

mutual
  def decode : (q a : T) → Option T
    | g _, _ => none
    | p _ (g _), _ => none
    | p _ (p _ (g _)), _ => none
    | p inner (p a' (p nested nested')), a =>
        match baseForward (p inner (p a' (p nested nested'))) a with
        | some base => some base
        | none =>
            if ha : a' = a then
              if hn : nested' = nested then
                preimage nested inner
              else none
            else none
  termination_by q _ => sz q
  decreasing_by simp_all [sz] <;> omega

  def preimage : (q r : T) → Option T
    | g _, _ => none
    | p _ (g _), _ => none
    | p _ (p _ (g _)), _ => none
    | p innerValue (p a (p nested nested')), r =>
        match baseBackward (p innerValue (p a (p nested nested'))) r with
        | some base => some base
        | none =>
            if hn : nested' = nested then
              match decode nested r with
              | some value => if value = innerValue then some a else none
              | none => none
            else none
  termination_by q _ => sz q
  decreasing_by simp_all [sz] <;> omega
end

theorem baseForward_sound {q a r : T} (h : baseForward q a = some r) :
    Code q a r := by
  cases q with
  | g n => simp [baseForward] at h
  | p left right =>
    cases left with
    | g n => simp [baseForward] at h
    | p b c =>
      cases right with
      | g n => simp [baseForward] at h
      | p a' rest =>
        cases rest with
        | g n => simp [baseForward] at h
        | p c' c'' =>
          simp only [baseForward] at h
          by_cases ha : a' = a
          · simp only [dif_pos ha] at h
            by_cases hc1 : c' = c
            · simp only [dif_pos hc1] at h
              by_cases hc2 : c'' = c
              · simp only [dif_pos hc2] at h
                injection h with hr
                subst r; subst a'; subst c'; subst c''
                exact Code.base a b c
              · simp only [dif_neg hc2] at h
                contradiction
            · simp only [dif_neg hc1] at h
              contradiction
          · simp only [dif_neg ha] at h
            contradiction

theorem baseBackward_sound {q r a : T} (h : baseBackward q r = some a) :
    Code q a r := by
  cases q with
  | g n => simp [baseBackward] at h
  | p left right =>
    cases left with
    | g n => simp [baseBackward] at h
    | p b c =>
      cases right with
      | g n => simp [baseBackward] at h
      | p a' rest =>
        cases rest with
        | g n => simp [baseBackward] at h
        | p c' c'' =>
          simp only [baseBackward] at h
          by_cases hb : b = r
          · simp only [dif_pos hb] at h
            by_cases hc1 : c' = c
            · simp only [dif_pos hc1] at h
              by_cases hc2 : c'' = c
              · simp only [dif_pos hc2] at h
                injection h with ha
                subst a; subst b; subst c'; subst c''
                exact Code.base a' r c
              · simp only [dif_neg hc2] at h
                contradiction
            · simp only [dif_neg hc1] at h
              contradiction
          · simp only [dif_neg hb] at h
            contradiction

mutual
  theorem decode_sound {q a r : T} (hresult : decode q a = some r) :
      Code q a r := by
    cases q with
    | g n => simp [decode] at hresult
    | p inner rest =>
      cases rest with
      | g n => simp [decode] at hresult
      | p a' rest' =>
        cases rest' with
        | g n => simp [decode] at hresult
        | p nested nested' =>
          cases hb : baseForward (p inner (p a' (p nested nested'))) a with
          | some base =>
              simp only [decode, hb] at hresult
              cases hresult
              exact baseForward_sound hb
          | none =>
              simp only [decode, hb] at hresult
              split at hresult <;> rename_i ha
              · split at hresult <;> rename_i hn
                · have innerProof := preimage_sound hresult
                  subst a'; subst nested'
                  simpa [W, S] using Code.succ innerProof a
                · contradiction
              · contradiction
  termination_by sz q
  decreasing_by simp_all [sz] <;> omega

  theorem preimage_sound {q r a : T} (hresult : preimage q r = some a) :
      Code q a r := by
    cases q with
    | g n => simp [preimage] at hresult
    | p innerValue rest =>
      cases rest with
      | g n => simp [preimage] at hresult
      | p outerInput rest' =>
        cases rest' with
        | g n => simp [preimage] at hresult
        | p nested nested' =>
          cases hb : baseBackward
              (p innerValue (p outerInput (p nested nested'))) r with
          | some base =>
              simp only [preimage, hb] at hresult
              cases hresult
              exact baseBackward_sound hb
          | none =>
              simp only [preimage, hb] at hresult
              split at hresult <;> rename_i hn
              · cases hd : decode nested r with
                | none => simp [hd] at hresult
                | some value =>
                  simp only [hd] at hresult
                  split at hresult <;> rename_i hv
                  · injection hresult with ha
                    subst a
                    have innerProof := decode_sound hd
                    subst value; subst nested'
                    simpa [W, S] using Code.succ innerProof outerInput
                  · contradiction
              · contradiction
  termination_by sz q
  decreasing_by simp_all [sz] <;> omega
end

theorem decoder_complete {q a r : T} (h : Code q a r) :
    decode q a = some r ∧ preimage q r = some a := by
  induction h with
  | base a b c =>
      constructor <;> simp [decode, preimage, baseForward, baseBackward, D, S]
  | @succ q c r h a ih =>
      rcases ih with ⟨hdecode, hpreimage⟩
      constructor
      · cases hb : baseForward (W r a q) a with
        | some base =>
            have hv : base = c :=
              code_right_unique (baseForward_sound hb) (Code.succ h a) rfl rfl
            simp only [W, S] at hb ⊢
            simp [decode, hb, hv]
        | none =>
            simp only [W, S] at hb ⊢
            simp [decode, hb, hpreimage]
      · cases hb : baseBackward (W r a q) c with
        | some base =>
            have hv : base = a :=
              code_left_unique (baseBackward_sound hb) (Code.succ h a) rfl rfl
            simp only [W, S] at hb ⊢
            simp [preimage, hb, hv]
        | none =>
            simp only [W, S] at hb ⊢
            simp [preimage, hb, hdecode]

def eval (a q : T) : T :=
  match decode q a with
  | some output => output
  | none => p a q

theorem eval_hit {q a r : T} (h : Code q a r) : eval a q = r := by
  have hd := (decoder_complete h).1
  simp [eval, hd]

theorem eval_raw {q a : T} (h : ¬ ∃ r, Code q a r) :
    eval a q = p a q := by
  cases hd : decode q a with
  | none => simp [eval, hd]
  | some r => exact (h ⟨r, decode_sound hd⟩).elim

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
  · rcases hx with ⟨r, hr⟩
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

instance instMagma : Magma T where
  op := eval

theorem source_holds (x y z : T) :
    x = y ◇ ((x ◇ z) ◇ (y ◇ (z ◇ z))) := by
  change x = eval y (eval (eval x z) (eval y (eval z z)))
  exact (source_eval x y z).symm

def gx : T := g 0
def gy : T := g 1
def gz : T := g 2
def gw : T := g 3

end T
end submission


open submission

namespace submission.T

theorem d10TargetRefutation
    (target : @EquationRHS T T.instMagma) : False := by
  first
  | have bad := target T.gx T.gy
    change (T.gx : T) = (T.eval (T.gx : T) (T.eval (T.gx : T) (T.gy : T))) at bad
    simpa [T.instMagma, T.gx, T.gy, T.gz, T.gw, T.eval, T.decode] using bad
  | have bad := target T.gx T.gz
    change (T.gx : T) = (T.eval (T.gx : T) (T.eval (T.gx : T) (T.gz : T))) at bad
    simpa [T.instMagma, T.gx, T.gy, T.gz, T.gw, T.eval, T.decode] using bad
  | have bad := target T.gx T.gw
    change (T.gx : T) = (T.eval (T.gx : T) (T.eval (T.gx : T) (T.gw : T))) at bad
    simpa [T.instMagma, T.gx, T.gy, T.gz, T.gw, T.eval, T.decode] using bad
  | have bad := target T.gy T.gx
    change (T.gy : T) = (T.eval (T.gy : T) (T.eval (T.gy : T) (T.gx : T))) at bad
    simpa [T.instMagma, T.gx, T.gy, T.gz, T.gw, T.eval, T.decode] using bad
  | have bad := target T.gy T.gz
    change (T.gy : T) = (T.eval (T.gy : T) (T.eval (T.gy : T) (T.gz : T))) at bad
    simpa [T.instMagma, T.gx, T.gy, T.gz, T.gw, T.eval, T.decode] using bad
  | have bad := target T.gy T.gw
    change (T.gy : T) = (T.eval (T.gy : T) (T.eval (T.gy : T) (T.gw : T))) at bad
    simpa [T.instMagma, T.gx, T.gy, T.gz, T.gw, T.eval, T.decode] using bad
  | have bad := target T.gz T.gx
    change (T.gz : T) = (T.eval (T.gz : T) (T.eval (T.gz : T) (T.gx : T))) at bad
    simpa [T.instMagma, T.gx, T.gy, T.gz, T.gw, T.eval, T.decode] using bad
  | have bad := target T.gz T.gy
    change (T.gz : T) = (T.eval (T.gz : T) (T.eval (T.gz : T) (T.gy : T))) at bad
    simpa [T.instMagma, T.gx, T.gy, T.gz, T.gw, T.eval, T.decode] using bad

end submission.T

def submission : Goal := by
  refine ⟨T, T.instMagma, ?_, ?_⟩
  · intro x y z
    exact T.source_holds x y z
  · intro target
    exact T.d10TargetRefutation target

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_9384_to_9 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_9384_to_9
