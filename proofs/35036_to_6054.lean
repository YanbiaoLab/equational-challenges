-- Equation35036 → Equation6054
-- Recorded verdict: false
-- Premise: x = ((y * z) * ((x * y) * x)) * y
-- Conclusion: x = y * (y * (z * ((w * x) * w)))
-- Original submission SHA-256: e68c994be55613087c536f2a830166db1977231030aa3db3bcc0f3cf3d749218
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ z) ◇ ((x ◇ y) ◇ x)) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ (y ◇ (z ◇ ((w ◇ x) ◇ w)))
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

inductive Code : T → T → T → Prop
  | base (output key z : T) :
      Code
        (p (p key z) (p (p output key) output))
        key output
  | aHit {key z a : T} (ha : Code key z a) (output : T) :
      Code
        (p a (p (p output key) output))
        key output
  | cHit {output key c : T} (hc : Code output key c) (z : T) :
      Code
        (p (p key z) (p c output))
        key output
  | both {key z a output c : T}
      (ha : Code key z a) (hc : Code output key c) :
      Code
        (p a (p c output))
        key output

theorem code_shape {q key output : T} (h : Code q key output) :
    ∃ left payload,
      q = p left (p payload output) ∧
      ((∃ z, left = p key z) ∨ (∃ z, Code key z left)) ∧
      (payload = p output key ∨ Code output key payload) := by
  cases h with
  | base output key z =>
      exact ⟨p key z, p output key, rfl, Or.inl ⟨z, rfl⟩,
        Or.inl rfl⟩
  | @aHit key z a ha output =>
      exact ⟨a, p output key, rfl, Or.inr ⟨z, ha⟩, Or.inl rfl⟩
  | @cHit output key c hc z =>
      exact ⟨p key z, c, rfl, Or.inl ⟨z, rfl⟩, Or.inr hc⟩
  | @both key z a output c ha hc =>
      exact ⟨a, c, rfl, Or.inr ⟨z, ha⟩, Or.inr hc⟩

theorem code_output_small {q key output : T} (h : Code q key output) :
    sz output < sz q := by
  cases h <;> simp [sz] <;> omega

theorem code_key_small {q key output : T} (h : Code q key output) :
    sz key < sz q := by
  induction h with
  | base output key z =>
      simp [sz] <;> omega
  | @aHit key z a ha output ih =>
      simp [sz] <;> omega
  | @cHit output key c hc z ih =>
      simp [sz] <;> omega
  | @both key z a output c ha hc iha ihc =>
      simp [sz] at * <;> omega

theorem code_output_unique {q key output₁ output₂ : T}
    (h₁ : Code q key output₁) (h₂ : Code q key output₂) :
    output₁ = output₂ := by
  rcases code_shape h₁ with ⟨left₁, payload₁, hq₁, _, _⟩
  rcases code_shape h₂ with ⟨left₂, payload₂, hq₂, _, _⟩
  have hq :
      p left₁ (p payload₁ output₁) =
        p left₂ (p payload₂ output₂) :=
    hq₁.symm.trans hq₂
  exact (p.inj (p.inj hq).2).2

noncomputable def eval (q key : T) : T := by
  classical
  exact if h : ∃ output, Code q key output
    then Classical.choose h
    else p q key

theorem eval_hit {q key output : T} (h : Code q key output) :
    eval q key = output := by
  rw [eval, dif_pos ⟨output, h⟩]
  exact code_output_unique (Classical.choose_spec ⟨output, h⟩) h

theorem eval_raw {q key : T} (h : ¬ ∃ output, Code q key output) :
    eval q key = p q key := by
  simp [eval, h]

theorem no_code_atom (n : Nat) (key : T) :
    ¬ ∃ output, Code (g n) key output := by
  rintro ⟨output, h⟩
  cases h

theorem no_code_pair_left (x y : T) :
    ¬ ∃ output, Code (p x y) x output := by
  rintro ⟨output, h⟩
  rcases code_shape h with
    ⟨left, payload, hq, hleft, hpayload⟩
  have houter := p.inj hq
  rcases hleft with ⟨z, hz⟩ | ⟨z, hz⟩
  · have hx : x = p x z := houter.1.trans hz
    have hs := congrArg sz hx
    simp [sz] at hs <;> omega
  · have hs := code_output_small hz
    rw [← houter.1] at hs
    omega

theorem no_code_after_hit {x y c : T} (h : Code x y c) :
    ¬ ∃ output, Code c x output := by
  rintro ⟨output, k⟩
  have hc := code_output_small h
  have hx := code_key_small k
  omega

theorem no_code_suffix_key (v key : T) :
    ¬ ∃ output, Code (p v key) key output := by
  rintro ⟨output, h⟩
  rcases code_shape h with
    ⟨left, payload, hq, hleft, hpayload⟩
  have hright : key = p payload output := (p.inj hq).2
  rcases hpayload with hpayload | hpayload
  · rw [hpayload] at hright
    have hs := congrArg sz hright
    simp [sz] at hs <;> omega
  · have hkey := code_key_small hpayload
    have hs := congrArg sz hright
    simp [sz] at hs <;> omega

theorem no_code_raw_B_returns_y (x y : T) :
    ¬ ∃ u, Code (p (p x y) x) u y := by
  rintro ⟨u, h⟩
  rcases code_shape h with
    ⟨left, payload, hq, hleft, hpayload⟩
  have houter := p.inj hq
  have hleft_eq : p x y = left := houter.1
  have hright_eq : x = p payload y := houter.2
  rcases hleft with ⟨z, hleft⟩ | ⟨z, hleft⟩
  · have hlu : p x y = p u z := hleft_eq.trans hleft
    have hxu : x = u := (p.inj hlu).1
    rcases hpayload with hpayload | hpayload
    · have hp : payload = p y u := hpayload
      rw [hp, ← hxu] at hright_eq
      have hs := congrArg sz hright_eq
      simp [sz] at hs <;> omega
    · have hu := code_key_small hpayload
      rw [← hxu] at hu
      have hs := congrArg sz hright_eq
      simp [sz] at hs <;> omega
  · have ha := code_output_small hleft
    rw [← hleft_eq] at ha
    rcases hpayload with hpayload | hpayload
    · have hs := congrArg sz hright_eq
      rw [hpayload] at hs
      simp [sz] at hs ha <;> omega
    · have hu := code_key_small hpayload
      have hs := congrArg sz hright_eq
      simp [sz] at hs ha <;> omega

theorem no_code_hit_B_returns_y {x y c : T} (h : Code x y c) :
    ¬ ∃ u, Code (p c x) u y := by
  rintro ⟨u, k⟩
  rcases code_shape k with
    ⟨left, payload, hq, hleft, hpayload⟩
  have hx : x = p payload y := (p.inj hq).2
  apply no_code_suffix_key payload y
  exact ⟨c, hx ▸ h⟩

def Step (x y value : T) : Prop :=
  value = p x y ∨ Code x y value

theorem step_y_small_B {x y value : T} (h : Step x y value) :
    sz y < sz (p value x) := by
  rcases h with h | h
  · rw [h]
    simp [sz] <;> omega
  · have hy := code_key_small h
    simp [sz] <;> omega

theorem no_code_step_B_returns_y {x y value : T}
    (h : Step x y value) :
    ¬ ∃ u, Code (p value x) u y := by
  rcases h with h | h
  · rw [h]
    exact no_code_raw_B_returns_y x y
  · exact no_code_hit_B_returns_y h

theorem no_code_B {x y value : T} (h : Step x y value) :
    ¬ ∃ output, Code value x output := by
  rcases h with h | h
  · rw [h]
    exact no_code_pair_left x y
  · exact no_code_after_hit h

theorem raw_A_implies_L_raw {x y z value : T}
    (hvalue : Step x y value) :
    ¬ ∃ output, Code (p y z) (p value x) output := by
  rintro ⟨output, h⟩
  rcases code_shape h with
    ⟨left, payload, hq, hleft, hpayload⟩
  have hy : y = left := (p.inj hq).1
  rcases hleft with ⟨u, hu⟩ | ⟨u, hu⟩
  · have he : y = p (p value x) u := hy.trans hu
    have hsmall := step_y_small_B hvalue
    have hs := congrArg sz he
    simp [sz] at hs hsmall <;> omega
  · apply no_code_step_B_returns_y hvalue
    refine ⟨u, ?_⟩
    rw [hy]
    exact hu

theorem hit_A_implies_L_raw {x y z a value : T}
    (ha : Code y z a) (hvalue : Step x y value) :
    ¬ ∃ output, Code a (p value x) output := by
  rintro ⟨output, h⟩
  have ha_small := code_output_small ha
  have hy_small := step_y_small_B hvalue
  have hB_small := code_key_small h
  omega

theorem source_eval (x y z : T) :
    eval (eval (eval y z) (eval (eval x y) x)) y = x := by
  by_cases hA : ∃ a, Code y z a
  · let a := Classical.choose hA
    have ha : Code y z a := Classical.choose_spec hA
    rw [eval_hit ha]
    by_cases hC : ∃ c, Code x y c
    · let c := Classical.choose hC
      have hc : Code x y c := Classical.choose_spec hC
      rw [eval_hit hc]
      rw [eval_raw (no_code_B (Or.inr hc))]
      rw [eval_raw (hit_A_implies_L_raw ha (Or.inr hc))]
      exact eval_hit (Code.both ha hc)
    · rw [eval_raw hC]
      rw [eval_raw (no_code_B (Or.inl rfl))]
      rw [eval_raw (hit_A_implies_L_raw ha (Or.inl rfl))]
      exact eval_hit (Code.aHit ha x)
  · rw [eval_raw hA]
    by_cases hC : ∃ c, Code x y c
    · let c := Classical.choose hC
      have hc : Code x y c := Classical.choose_spec hC
      rw [eval_hit hc]
      rw [eval_raw (no_code_B (Or.inr hc))]
      rw [eval_raw (raw_A_implies_L_raw (z := z) (Or.inr hc))]
      exact eval_hit (Code.cHit hc z)
    · rw [eval_raw hC]
      rw [eval_raw (no_code_B (Or.inl rfl))]
      rw [eval_raw (raw_A_implies_L_raw (z := z) (Or.inl rfl))]
      exact eval_hit (Code.base x y z)

noncomputable instance instMagma : Magma T where
  op := eval

theorem source_holds (x y z : T) :
    x = ((y ◇ z) ◇ ((x ◇ y) ◇ x)) ◇ y := by
  change x = eval (eval (eval y z) (eval (eval x y) x)) y
  exact (source_eval x y z).symm

def gx : T := g 0
def gy : T := g 1
def gz : T := g 2
def gw : T := g 3

theorem eval_atom (n : Nat) (key : T) :
    eval (g n) key = p (g n) key :=
  eval_raw (no_code_atom n key)

theorem eval_pair_left (x y : T) :
    eval (p x y) x = p (p x y) x :=
  eval_raw (no_code_pair_left x y)

theorem target6054_value :
    gy ◇ (gy ◇ (gz ◇ ((gw ◇ gx) ◇ gw))) =
      p gy (p gy (p gz (p (p gw gx) gw))) := by
  change
    eval gy (eval gy (eval gz (eval (eval gw gx) gw))) =
      p gy (p gy (p gz (p (p gw gx) gw)))
  simp [gx, gy, gz, gw, eval_atom, eval_pair_left]

theorem bad6054 :
    gx ≠ gy ◇ (gy ◇ (gz ◇ ((gw ◇ gx) ◇ gw))) := by
  rw [target6054_value]
  intro h
  cases h

theorem target12757_value :
    gx ◇ ((gy ◇ (gz ◇ (gz ◇ gz))) ◇ gy) =
      p gx (p (p gy (p gz (p gz gz))) gy) := by
  change
    eval gx (eval (eval gy (eval gz (eval gz gz))) gy) =
      p gx (p (p gy (p gz (p gz gz))) gy)
  simp [gx, gy, gz, eval_atom, eval_pair_left]

theorem bad12757 :
    gx ≠ gx ◇ ((gy ◇ (gz ◇ (gz ◇ gz))) ◇ gy) := by
  rw [target12757_value]
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
    exact T.bad6054 (target T.gx T.gy T.gz T.gw)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_35036_to_6054 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_35036_to_6054
