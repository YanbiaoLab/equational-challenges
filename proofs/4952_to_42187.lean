-- Equation4952 → Equation42187
-- Recorded verdict: false
-- Premise: x = y ◇ (x ◇ (y ◇ (y ◇ (z ◇ y))))
-- Conclusion: x ◇ y = z ◇ (y ◇ (w ◇ (u ◇ v)))
-- Original submission SHA-256: 62ff36c7af1ca9b9b37e99a8f876e447451f8e408680a93bba7b709c9b445bdb
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ (y ◇ (y ◇ (z ◇ y))))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x ◇ y = z ◇ (y ◇ (w ◇ (u ◇ v)))
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Original submission body
-- stage:stage0_generalized_infinite_source_family
-- d14-direct-template
                   
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
  | base (output owner z : T) :
      Code owner
        (p output (p owner (p owner (p z owner)))) output
  | hit {output owner z hitValue : T}
      (h : Code z owner hitValue) :
      Code owner
        (p output (p owner (p owner hitValue))) output
theorem code_spine {first second output : T}
    (h : Code first second output) :
    ∃ last,
      second = p output (p first (p first last)) := by
  cases h with
  | base output owner z =>
      exact ⟨p z _, rfl⟩
  | @hit output owner z hitValue h =>
      exact ⟨hitValue, rfl⟩
theorem code_cases {first second output : T}
    (h : Code first second output) :
    (∃ z,
      second =
        p output
          (p first (p first (p z first)))) ∨
    (∃ z hitValue,
      second =
          p output (p first (p first hitValue)) ∧
        Code z first hitValue) := by
  cases h with
  | base output owner z =>
      exact Or.inl ⟨z, rfl⟩
  | @hit output owner z hitValue h =>
      exact Or.inr ⟨z, hitValue, rfl, h⟩
theorem code_output_unique {first second output₁ output₂ : T}
    (h₁ : Code first second output₁)
    (h₂ : Code first second output₂) :
    output₁ = output₂ := by
  rcases code_spine h₁ with ⟨last₁, hshape₁⟩
  rcases code_spine h₂ with ⟨last₂, hshape₂⟩
  exact (p.inj (hshape₁.symm.trans hshape₂)).1
theorem code_output_small {first second output : T}
    (h : Code first second output) :
    sz output < sz second := by
  rcases code_spine h with ⟨last, rfl⟩
  simp [sz] <;> omega
theorem code_first_small {first second output : T}
    (h : Code first second output) :
    sz first < sz second := by
  rcases code_spine h with ⟨last, rfl⟩
  simp [sz] <;> omega
theorem no_code_if_second_le_first {first second : T}
    (hsize : sz second ≤ sz first) :
    ¬ ∃ output, Code first second output := by
  rintro ⟨output, h⟩
  have hsmall := code_first_small h
  omega
theorem no_code_same (q : T) :
    ¬ ∃ output, Code q q output :=
  no_code_if_second_le_first (Nat.le_refl _)
theorem no_code_output_second {first second : T} :
    ¬ Code first second second := by
  intro h
  have hsmall := code_output_small h
  omega
noncomputable def eval (first second : T) : T := by
  classical
  exact if h : ∃ output, Code first second output
    then Classical.choose h
    else p first second
theorem eval_hit {first second output : T}
    (h : Code first second output) :
    eval first second = output := by
  rw [eval, dif_pos ⟨output, h⟩]
  exact code_output_unique
    (Classical.choose_spec ⟨output, h⟩) h
theorem eval_raw {first second : T}
    (h : ¬ ∃ output, Code first second output) :
    eval first second = p first second := by
  simp [eval, h]
theorem no_code_raw_first (owner z : T) :
    ¬ ∃ output, Code owner (p z owner) output := by
  rintro ⟨output, h⟩
  rcases code_spine h with ⟨last, hshape⟩
  have hcycle :
      owner = p owner (p owner last) :=
    (p.inj hshape).2
  have hsize := congrArg sz hcycle
  simp [sz] at hsize <;> omega
theorem no_code_raw_second (owner z : T) :
    ¬ ∃ output,
      Code owner (p owner (p z owner)) output := by
  rintro ⟨output, h⟩
  rcases code_spine h with ⟨last, hshape⟩
  have htail :
      p z owner =
        p owner (p owner last) :=
    (p.inj hshape).2
  have hz : z = owner := (p.inj htail).1
  subst z
  have hcycle :
      owner = p owner last :=
    (p.inj htail).2
  have hsize := congrArg sz hcycle
  simp [sz] at hsize <;> omega
theorem no_code_raw_third (x owner z : T) :
    ¬ ∃ output,
      Code x
        (p owner (p owner (p z owner))) output := by
  rintro ⟨output, h⟩
  rcases code_cases h with
      ⟨q, hshape⟩ |
      ⟨q, hitValue, hshape, hrec⟩
  · have hout : owner = output := (p.inj hshape).1
    subst output
    have htail :
        p owner (p z owner) =
          p x (p x (p q x)) :=
      (p.inj hshape).2
    have howner : owner = x := (p.inj htail).1
    subst owner
    have hrest :
        p z x = p x (p q x) :=
      (p.inj htail).2
    have hz : z = x := (p.inj hrest).1
    subst z
    have hcycle : x = p q x :=
      (p.inj hrest).2
    have hsize := congrArg sz hcycle
    simp [sz] at hsize <;> omega
  · have hout : owner = output := (p.inj hshape).1
    subst output
    have htail :
        p owner (p z owner) =
          p x (p x hitValue) :=
      (p.inj hshape).2
    have howner : owner = x := (p.inj htail).1
    subst owner
    have hrest :
        p z x = p x hitValue :=
      (p.inj htail).2
    have hz : z = x := (p.inj hrest).1
    subst z
    have hhit : x = hitValue := (p.inj hrest).2
    subst hitValue
    exact no_code_output_second hrec
theorem no_code_after_hit_first {z owner hitValue : T}
    (h : Code z owner hitValue) :
    ¬ ∃ output, Code owner hitValue output := by
  rintro ⟨output, k⟩
  have hsmall := code_output_small h
  have ksmall := code_first_small k
  omega
theorem no_code_after_hit_second {z owner hitValue : T}
    (h : Code z owner hitValue) :
    ¬ ∃ output,
      Code owner (p owner hitValue) output := by
  rintro ⟨output, k⟩
  rcases code_spine k with ⟨last, hshape⟩
  have htail :
      hitValue = p owner (p owner last) :=
    (p.inj hshape).2
  have hsmall := code_output_small h
  have hsize := congrArg sz htail
  simp [sz] at hsize <;> omega
theorem no_code_after_hit_third {z owner hitValue : T}
    (h : Code z owner hitValue) (sourceOutput : T) :
    ¬ ∃ output,
      Code sourceOutput
        (p owner (p owner hitValue)) output := by
  rintro ⟨output, k⟩
  rcases code_spine k with ⟨last, hshape⟩
  have hout : owner = output := (p.inj hshape).1
  subst output
  have htail :
      p owner hitValue =
        p sourceOutput (p sourceOutput last) :=
    (p.inj hshape).2
  have howner : owner = sourceOutput :=
    (p.inj htail).1
  subst sourceOutput
  have hhit :
      hitValue = p owner last :=
    (p.inj htail).2
  have hsmall := code_output_small h
  have hsize := congrArg sz hhit
  simp [sz] at hsize <;> omega
theorem source_eval (x owner z : T) :
    eval owner
      (eval x
        (eval owner
          (eval owner
            (eval z owner)))) = x := by
  by_cases hcollision : ∃ hitValue, Code z owner hitValue
  · let hitValue := Classical.choose hcollision
    have hhit : Code z owner hitValue :=
      Classical.choose_spec hcollision
    rw [eval_hit hhit]
    rw [eval_raw (no_code_after_hit_first hhit)]
    rw [eval_raw (no_code_after_hit_second hhit)]
    rw [eval_raw (no_code_after_hit_third hhit x)]
    exact eval_hit (Code.hit (output := x) hhit)
  · rw [eval_raw hcollision]
    rw [eval_raw (no_code_raw_first owner z)]
    rw [eval_raw (no_code_raw_second owner z)]
    rw [eval_raw (no_code_raw_third x owner z)]
    exact eval_hit (Code.base x owner z)
noncomputable instance instMagma : Magma T where
  op := eval
theorem source_holds (x y z : T) :
    x = y ◇ (x ◇ (y ◇ (y ◇ (z ◇ y)))) := by
  change
    x =
      eval y
        (eval x
          (eval y
            (eval y
              (eval z y))))
  exact (source_eval x y z).symm
def g0 : T := g 0
def q : T := p g0 g0
def r : T := p g0 q
def s : T := p q g0
theorem no_code_g0_q :
    ¬ ∃ output, Code g0 q output := by
  rintro ⟨output, h⟩
  rcases code_spine h with ⟨last, hshape⟩
  have hcycle :
      g0 = p g0 (p g0 last) :=
    (p.inj hshape).2
  cases hcycle
theorem gg_value : eval g0 g0 = q := by
  exact eval_raw (no_code_same g0)
theorem gq_value : eval g0 q = r := by
  exact eval_raw no_code_g0_q
theorem qg_value : eval q g0 = s := by
  apply eval_raw
  apply no_code_if_second_le_first
  simp [q, g0, sz]
theorem rs_value : eval r s = p r s := by
  apply eval_raw
  apply no_code_if_second_le_first
  simp [r, s, q, g0, sz]
end T
end submission
open submission
namespace submission
namespace T
def IsGenerator : T → Prop
  | .g _ => True
  | .p _ _ => False
def g1 : T := g 1
def c3 : T := p g0 r
def c4 : T := p g0 c3
def a : T := p g1 q
def b : T := p g0 a
def c : T := p g0 b
def d : T := p g1 c
theorem no_code_second_atom (first : T) (index : Nat) :
    ¬ ∃ output, Code first (g index) output := by
  rintro ⟨output, h⟩
  rcases code_spine h with ⟨last, hshape⟩
  cases hshape
theorem no_code_g0_r : ¬ ∃ output, Code g0 r output := by
  rintro ⟨output, h⟩
  rcases code_spine h with ⟨last, hshape⟩
  simp [r, q, g0] at hshape
theorem no_code_g0_c3 : ¬ ∃ output, Code g0 c3 output := by
  rintro ⟨output, h⟩
  rcases code_cases h with
      ⟨z, hbase⟩ |
      ⟨z, hitValue, hshape, hrec⟩
  · simp [c3, r, q, g0] at hbase
  · have htail1 : r = p g0 (p g0 hitValue) :=
      (p.inj hshape).2
    have htail2 : q = p g0 hitValue :=
      (p.inj htail1).2
    have hhit : g0 = hitValue :=
      (p.inj htail2).2
    subst hitValue
    exact no_code_second_atom z 0 ⟨g0, hrec⟩
theorem gr_value : eval g0 r = c3 := by
  exact eval_raw no_code_g0_r
theorem gc3_value : eval g0 c3 = c4 := by
  exact eval_raw no_code_g0_c3
theorem c3g_value : eval c3 g0 = p c3 g0 := by
  apply eval_raw
  apply no_code_if_second_le_first
  simp [c3, r, q, g0, sz]
theorem g1q_value : eval g1 q = a := by
  apply eval_raw
  rintro ⟨output, h⟩
  rcases code_spine h with ⟨last, hshape⟩
  simp [g1, q, g0] at hshape
theorem g0a_value : eval g0 a = b := by
  apply eval_raw
  rintro ⟨output, h⟩
  rcases code_spine h with ⟨last, hshape⟩
  simp [a, g1, q, g0] at hshape
theorem g0b_value : eval g0 b = c := by
  apply eval_raw
  rintro ⟨output, h⟩
  rcases code_spine h with ⟨last, hshape⟩
  simp [b, a, g1, q, g0] at hshape
theorem g1c_value : eval g1 c = d := by
  apply eval_raw
  rintro ⟨output, h⟩
  rcases code_spine h with ⟨last, hshape⟩
  simp [c, b, a, g1, q, g0] at hshape
end T
end submission
open submission
noncomputable def submission : Goal := by
  refine ⟨T, T.instMagma, ?_, ?_⟩
  · intro x y z
    exact T.source_holds x y z
  · intro target
    first
    | have bad := target T.g0 T.g0 T.g0 T.g1 T.g0 T.g0
      change (T.eval (T.g0 : T) (T.g0 : T)) = (T.eval (T.g0 : T) (T.eval (T.g0 : T) (T.eval (T.g1 : T) (T.eval (T.g0 : T) (T.g0 : T))))) at bad
      rw [T.gg_value, T.g1q_value, T.g0a_value, T.g0b_value] at bad
      exact nomatch bad

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_4952_to_42187 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_4952_to_42187
