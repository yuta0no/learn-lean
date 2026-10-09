def Implies (p q : Prop) : Prop := p → q

#check And
#check Or
#check Not
#check Implies

variable (p q r : Prop)
#check And p q
#check Or (And p q) r
#check Implies (And p q) (And q p)

structure Proof (p : Prop) : Type where
  proof : p

#check Proof

axiom and_commut (p q : Prop) : Proof (Implies (And p q) (And q p))
variable (p q : Prop)

#check and_commut p q

axiom modus_ponens (p q : Prop) :
  Proof (Implies p q) → Proof p → Proof q

axiom implies_intro (p q : Prop) :
  (Proof p → Proof q) → Proof (Implies p q)


set_option linter.unusedVariables false
---
variable {p : Prop}
variable {q : Prop}

theorem t1 : p → q → p := fun hp : p => fun hq : q => hp

theorem t1_ : p → q → p :=
  fun hp : p =>
  fun hq : q =>
  show p from hp

theorem t1__ : p → q → p :=
  fun hp _ => hp

axiom hp : p
#check hp
theorem t2 : q → p := t1 hp

variable (p q : Prop)

example (hp : p) (hq : q) : p ∧ q := And.intro hp hq
example (h : p ∧ q) : p := And.left h
example (h : p ∧ q) : q := And.right h
example (h : p ∧ q) : q ∧ p := And.intro (And.right h) (And.left h)

variable (hp : p) (hq : q)
#check (⟨hp, hq⟩ : p ∧ q)
example (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩

example (h : p ∧ q) : q ∧ p := ⟨h.right, h.left⟩

variable (p q r : Prop)
example (h : p ∨ q) : q ∨ p :=
  Or.elim h
    (fun hp : p => show q ∨ p from Or.intro_right q hp)
    (fun hq : q => show q ∨ p from Or.intro_left p hq)

example (hpq : p → q) (hnq : ¬q) : ¬p :=
  fun hp : p =>
  show False from hnq (hpq hp)

example (hp : p) (hnp : ¬p) : q := absurd hp hnp
example (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
  absurd (hqp hq) hnp

theorem and_swap : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q => show q ∧ p from ⟨h.right, h.left⟩)
    (fun h : q ∧ p => show p ∧ q from ⟨h.right, h.left⟩)

#check and_swap p q

variable (h : p ∧ q)
example : q ∧ p := Iff.mp (and_swap p q) h

example (h : p ∧ q) : q ∧ p := (and_swap p q).mp h
example (h : q ∧ p) : p ∧ q := (and_swap p q).mpr h

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  have hq : q := h.right
  show q ∧ p from And.intro hq hp

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  have hq : q := h.right
  show q ∧ p from ⟨hq, hp⟩

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  suffices hq : q from And.intro hq hp
  show q from And.right h

open Classical
variable (p : Prop)
#check em p

theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)

example (h : ¬¬p) : p :=
  byCases
    (fun h₁ : p => h₁)
    (fun h₁ : ¬p => absurd h₁ h)

example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
  Or.elim (em p)
    (fun hp : p =>
      Or.inr
        (show ¬q from
          fun hq : q =>
          h ⟨hp, hq⟩)
    )
    (fun hp : ¬p =>
      Or.inl hp)


example (p q : Prop) : ¬(p ∧ ¬q) → (p → q) :=
  fun h : ¬(p ∧ ¬q) =>
  fun hp : p =>
  show q from
    Or.elim (em q)
    (fun hq : q => hq)
    (fun hnq : ¬q => absurd ⟨hp, hnq⟩ h)

-- Excercise

variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun ⟨hp, hq⟩ => ⟨hq, hp⟩)
    (fun ⟨hp, hq⟩ => ⟨hq, hp⟩)

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h => Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq))
    (fun h => Or.elim h (fun hq => Or.inr hq) (fun hp => Or.inl hp))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun h => ⟨h.left.left, ⟨h.left.right, h.right⟩⟩)
    (fun h => ⟨⟨h.left, h.right.left⟩, h.right.right⟩)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun hpqr : ((p ∨ q) ∨ r) =>
      Or.elim hpqr
        (fun hpq => Or.elim hpq (fun hp => Or.inl hp) (fun hq => Or.inr (Or.inl hq)))
        (fun hr => Or.inr (Or.inr hr))
    )
    (
      fun hpqr : (p ∨ (q ∨ r)) =>
        Or.elim hpqr
          (fun hp => Or.inl (Or.inl hp))
          (fun hqr => Or.elim hqr (fun hq => Or.inl (Or.inr hq)) (fun hr => Or.inr hr))
    )

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h : p ∧ (q ∨ r) =>
      have hp : p := h.left
      Or.elim (h.right) (fun hq => Or.inl ⟨hp, hq⟩) (fun hr => Or.inr ⟨hp, hr⟩)
    )
    (fun h : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim (h) (fun hpq => ⟨hpq.left, Or.inl hpq.right⟩) (fun hpr => ⟨hpr.left, Or.inr hpr.right⟩)
    )

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (fun h : p ∨ (q ∧ r) =>
      Or.elim h (fun hp : p => ⟨Or.inl hp, Or.inl hp⟩) (fun hqr : q ∧ r => ⟨Or.inr hqr.left, Or.inr hqr.right⟩)
    )
    (fun h : (p ∨ q) ∧ (p ∨ r) =>
      have hpq : p ∨ q := h.left
      have hpr : p ∨ r := h.right
      Or.elim (hpq) (fun hp => Or.inl hp) (fun hq =>
      Or.elim (hpr) (fun hp => Or.inl hp) (fun hr => Or.inr ⟨hq, hr⟩)
    ))

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (fun h ⟨hp, hq⟩ => h hp hq)
    (fun h hp hq => h ⟨hp, hq⟩)

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (fun h => ⟨fun hp => h (Or.inl hp), fun hq => h (Or.inr hq)⟩)
    (fun ⟨hpr, hqr⟩ hpq => Or.elim (hpq) (fun hp : p => hpr hp) (fun hq : q => hqr hq))

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (fun h => ⟨fun hp : p => h (Or.inl hp), fun hq : q => h (Or.inr hq)⟩)
    (fun ⟨hnp, hnq⟩ h => Or.elim h hnp hnq)

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  fun h ⟨hp, hq⟩ => Or.elim h (fun hnp => hnp hp) (fun hnq => hnq hq)

example : ¬(p ∧ ¬p) :=
  fun ⟨hp, hnp⟩ => hnp hp

example : p ∧ ¬q → ¬(p → q) :=
  fun ⟨hp, hnq⟩ hpq => absurd (hpq hp) hnq

example : ¬p → (p → q) :=
  fun hnp hp => absurd hp hnp

example : (¬p ∨ q) → (p → q) :=
  fun hnp_q hp => Or.elim (hnp_q) (fun hnp : ¬p => absurd hp hnp) (fun hq : q => hq)

example : p ∨ False ↔ p :=
  Iff.intro
    (fun hpf => Or.elim hpf (fun hp => hp) (fun hf => absurd hf (fun h => h)))
    (fun hp => Or.inl hp)

example : p ∧ False ↔ False :=
  Iff.intro
    (fun ⟨hp, hf⟩ => hf)
    (fun hf => hf.elim)

example : (p → q) → (¬q → ¬p) :=
  fun hpq hnq => Or.elim (em p) (fun hp : p => absurd (hpq hp) hnq ) (fun hnp => hnp)


-- Review

example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun h => ⟨h.left.left, ⟨h.left.right, h.right⟩⟩)
    (fun h => ⟨⟨h.left, h.right.left⟩, h.right.right⟩)

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
  (fun h : (p ∨ q) → r => ⟨fun hp : p => h (Or.inl hp), fun hq : q => h (Or.inr hq)⟩)
  (fun ⟨hpr, hqr⟩ hpq => Or.elim hpq (fun hp => hpr hp) (fun hq => hqr hq))

example : (¬p ∨ q) → (p → q) :=
  fun h hp => Or.elim h (fun hnp => absurd hp hnp) (fun hq => hq)
