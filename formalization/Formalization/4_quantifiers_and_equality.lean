example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
  fun h => fun y : α => show p y from (h y).left

variable (α : Type) (r : α → α → Prop)

variable (refl_r : ∀ x, r x x)
variable (symm_r : ∀ {x y}, r x y → r y x)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
  trans_r (trans_r hab (symm_r hcb)) hcd

#check Eq.refl
#check Eq.symm
#check Eq.trans

universe u
#check @Eq.refl.{u}
#check @Eq.symm.{u}
#check @Eq.trans.{u}


variable (α : Type) (a b c d : α)
variable (hab : a = b) (hcb : c = b) (hcd : c = d)

example : a = d :=
  Eq.trans hab (Eq.trans (Eq.symm hcb) hcd)

example : a = d :=
  (hab.trans hcb.symm).trans hcd

variable (α β : Type)

example (f : α → β) (a : α) : (fun x => f x) a = f a := Eq.refl _
example (a : α) (b : β) : (a, b).1 = a := Eq.refl _
example : 2 + 3 = 5 := Eq.refl _

example (f : α → β) (a : α) : (fun x => f x) a = f a := rfl

example (α : Type) (a b : α) (p : α → Prop)
        (h1 : a = b) (h2 : p a) : p b :=
  Eq.subst h1 h2

example (α : Type) (a b : α) (p : α → Prop)
        (h1 : a = b) (h2 : p a) : p b :=
  h1 ▸ h2

example (x y : Nat) :
  (x + y) * (x + y) =
  x * x + y * x + x * y + y * y :=
  have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y := Nat.mul_add (x + y) x y
  have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y) :=
    (Nat.add_mul x y x) ▸ (Nat.add_mul x y y) ▸ h1
  h2.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm

variable (a b c d e : Nat)
theorem T
  (h1 : a = b)
  (h2 : b = c + 1)
  (h3 : c = d)
  (h4 : e = 1 + d) :
  a = e :=
  calc
    a = b     := h1
    _ = c + 1 := h2
    _ = d + 1 := congrArg Nat.succ h3
    _ = 1 + d := Nat.add_comm d 1
    _ = e     := Eq.symm h4


variable (a b c d e : Nat)
theorem T1
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
  calc
    a = b      := by rw [h1]
    _ = c + 1  := by rw [h2]
    _ = d + 1  := by rw [h3]
    _ = 1 + d  := by rw [Nat.add_comm]
    _ = e      := by rw [h4]

variable (a b c d : Nat)
example (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
  calc
    a = b     := h1
    _ ≤ c     := h2
    _ < c + 1 := Nat.lt_succ_self c
    _ < d     := h3


def divides (x y : Nat) : Prop :=
  ∃ k, k*x = y


theorem divides_trans (h₁ : divides x y) (h₂ : divides y z) : divides x z :=
  let ⟨k₁, d₁⟩ := h₁
  let ⟨k₂, d₂⟩ := h₂
  ⟨k₁ * k₂, by rw [Nat.mul_comm k₁ k₂, Nat.mul_assoc, d₁, d₂]⟩


theorem divides_mul (x : Nat) (k : Nat) : divides x (k*x) :=
  ⟨k, rfl⟩


instance : Trans divides divides divides where
  trans := divides_trans

variable  (x y z : Nat)
example (h₁ : divides x y) (h₂ : y = z) : divides x (2 * z) :=
  calc
    divides x y := h₁
    _ = z := h₂
    divides _ (2*z) := divides_mul ..

infix:50 " | " => divides

example (h₁ : divides x y) (h₂ : y = z) : divides x (2*z) :=
  calc
    x | y   := h₁
    _ = z   := h₂
    _ | 2*z := divides_mul ..


example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  Exists.intro 1 h

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  Exists.intro 0 h

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  ⟨0, h⟩

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  Exists.intro y ⟨hxy, hyz⟩

variable (α : Type) (p q : α → Prop)
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h
    (fun w =>
     fun hw : p w ∧ q w =>
     show ∃ x, q x ∧ p x from ⟨w, hw.right, hw.left⟩
    )

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨(w : α), (hw : p w ∧ q w)⟩ => ⟨w, hw.right, hw.left⟩

def IsEven (a : Nat) := ∃ b, a = 2 * b

theorem even_plus_even (h1 : IsEven a) (h2 : IsEven b) : IsEven (a + b) :=
  Exists.elim h1 (fun (w1 : Nat) (hw1 : a = 2 * w1) =>
  Exists.elim h2 (fun (w2 : Nat) (hw2 : b = 2 * w2) =>
    Exists.intro (w1 + w2)
      (calc a + b
        _ = 2 * w1 + 2 * w2 := by rw [hw1, hw2]
        _ = 2 * (w1 + w2) := by rw [Nat.mul_add]
      )
    )
  )

open Classical
variable (p : α → Prop)

-- TODO: review
example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
  byContradiction
    (
      fun h1 : ¬ ∃ x, p x =>
        have h2 : ∀ x, ¬ p x :=
          fun x =>
          fun h3 : p x =>
          have h4 : ∃ x, p x := ⟨x, h3⟩
          show False from h1 h4
        show False from h h2)


-- exercise

open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ _x : α, r) → r :=
  fun ⟨_w, hr⟩ => hr

example (a : α) : r → (∃ _x : α, r) :=
  fun hr : r => ⟨a, hr⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
  (fun h => Exists.elim h (fun w hw => ⟨⟨w, hw.left⟩, hw.right⟩))
  (fun ⟨h, hr⟩ => Exists.elim h (fun w hw => ⟨w, ⟨hw, hr⟩⟩))

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
  (fun h => Exists.elim h (fun w hw => Or.elim (hw)
    (fun hpw => Or.inl ⟨w, hpw⟩)
    (fun hqw => Or.inr ⟨w, hqw⟩)
    )
  )
  (fun h => Or.elim h
    (fun hex => Exists.elim hex (fun w hpw => ⟨w, Or.inl hpw⟩))
    (fun hex => Exists.elim hex (fun w hqw => ⟨w, Or.inr hqw⟩))
  )

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro
  (fun h ⟨w, hnp⟩ => hnp (h w))
  (fun h x => byContradiction
    (fun hnp : ¬ p x =>
      have h_ex : ∃ x, ¬ p x := ⟨x, hnp⟩
      show False from h h_ex
    )
  )

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  Iff.intro
  (fun hp hnp => Exists.elim hp (fun w hpw => absurd hpw (hnp w)))
  (fun h => byContradiction
    (fun h1 : ¬ ∃ x, p x =>
      have h2 : ∀ x, ¬ p x := fun x hpw => h1 ⟨x, hpw⟩
      absurd h2 h
    )
  )

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  Iff.intro
  (fun h x hp => h ⟨x, hp⟩)
  (fun h ⟨x, hp⟩ => (h x) hp)

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  Iff.intro
  (fun h => byContradiction
    (fun hnenp : ¬ ∃ x, ¬ p x =>
      have h1 : ∀ x, p x :=
        fun x =>
          byContradiction
            (fun hnp : ¬ p x => hnenp ⟨x, hnp⟩)
      h h1
    )
  )
  (fun ⟨w, hnw⟩ h => absurd (h w) hnw)

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  Iff.intro
  (fun hpr hp => Exists.elim hp (fun w hpw => (hpr w) hpw))
  (fun h x hpw => h ⟨x, hpw⟩)

-- TODO: review
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
  (fun (h : ∃ x, p x → r) hp => Exists.elim h (fun w hpwr => hpwr (hp w)))
  (fun h => Or.elim (em (∀ x, p x))
    (fun hap : ∀ x, p x => ⟨a, fun _ => h hap⟩)
    (fun hnap : ¬ ∀ x, p x =>
      byContradiction
      (fun hneqpxr : ¬ ∃ x, p x → r =>
        have hap : ∀ x, p x := fun x =>
          byContradiction (fun hnp : ¬ p x => hneqpxr ⟨x, fun hpx => absurd hpx hnp⟩)
      absurd hap hnap
      )
    )
  )

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  Iff.intro
  (fun ⟨w, hrpw⟩ hr => ⟨w, hrpw hr⟩)
  (fun h => Or.elim (em (p a))
    (fun hpa : p a => ⟨a, fun _ => hpa⟩)
    (fun _hnpa : ¬ p a => byContradiction
      (
        fun hne : ¬ ∃ x, r → p x =>
        have hnr : r → False := fun hr =>
          Exists.elim (h hr) (fun w hpw => hne ⟨w, fun _ => hpw⟩)
        have hrpa : r → p a := fun hr => False.elim (hnr hr)
        hne ⟨a, hrpa⟩
      )
    )
  )


example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  Iff.intro
  (fun h hr => Exists.elim h (fun w hw => ⟨w, hw hr⟩))
  (fun h => Or.elim (em r)
    (fun hr => Exists.elim (h hr) (fun w pw => ⟨w, fun _ => pw⟩))
    (fun hnr => ⟨a, fun hr => absurd hr hnr⟩)
  )

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  Iff.intro
  (fun h hr => Exists.elim h (fun w hw => ⟨w, hw hr⟩))
  (fun h => Or.elim (em r)
    (fun hr : r => Exists.elim (h hr) (fun w hpw => ⟨w, fun _hr => hpw⟩))
    (fun hnr : ¬r => ⟨a, fun hr => absurd hr hnr⟩)
  )


example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
  (fun h h_ex => Exists.elim (h) (fun w hpwr => hpwr (h_ex w)))
  (fun h => Or.elim (em (∀ x, p x))
    (fun h_ax : ∀ x, p x => ⟨a, fun _ => h h_ax⟩)
    (fun h_nax : ¬∀ x, p x => byContradiction
      (fun h_nex : ¬∃ x, p x → r =>
        have h_ax : ∀ x, p x := fun x =>
          byContradiction (fun h_npx : ¬ p x => h_nex ⟨x, fun h_px => absurd h_px h_npx⟩)
        absurd h_ax h_nax
      )
    )
  )

-- solution by Gemini Flash 3.6
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (fun h h_ex => Exists.elim h (fun w hpwr => hpwr (h_ex w)))
    (fun h =>
      byCases
        (fun h_ex : ∃ x, ¬ p x =>
          let ⟨w, hnp⟩ := h_ex
          ⟨w, fun hp => absurd hp hnp⟩)
        (fun h_nex : ¬ ∃ x, ¬ p x =>
          have h_all : ∀ x, p x := fun x =>
            byCases
              (fun hp : p x => hp)
              (fun hnp : ¬ p x => absurd ⟨x, hnp⟩ h_nex)
          have hr : r := h h_all
          ⟨a, fun _ => hr⟩)
    )

-- Section 4.5

variable (f : Nat → Nat)
variable (h : ∀ x : Nat, f x ≤ f (x + 1))

example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans this (h 1)
  show f 0 ≤ f 3 from Nat.le_trans this (h 2)

example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans (by assumption) (h 1)
  show f 0 ≤ f 3 from Nat.le_trans (by assumption) (h 2)

example : f 0 ≥ f 1 → f 1 ≥ f 2 → f 0 = f 2 :=
  fun _ : f 0 ≥ f 1 =>
  fun _ : f 1 ≥ f 2 =>
  have : f 0 ≥ f 2 := Nat.le_trans ‹f 1 ≥ f 2› ‹f 0 ≥ f 1›
  have : f 0 ≤ f 2 := Nat.le_trans (h 0) (h 1)
  show f 0 = f 2 from Nat.le_antisymm this ‹f 0 ≥ f 2›


-- Section 4.6 Exercises

-- 1
variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
  (fun (hpq : ∀ x, p x ∧ q x) => ⟨fun x => (hpq x).left, fun x => (hpq x).right⟩)
  (fun ⟨hp, hq⟩ => fun x => ⟨hp x, hq x⟩)

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun hpq hp => fun x => (hpq x) (hp x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun h => Or.elim h
  (fun hp : ∀ x, p x => fun x => Or.inl (hp x))
  (fun hq : ∀ x, q x => fun x => Or.inr (hq x))


-- 2
variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) :=
  fun ha => Iff.intro
  (fun har => har ha)
  (fun hr => fun _ => hr)

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
  (fun h => Or.elim (em r)
    (fun hr : r => Or.inr hr)
    (fun hnr : ¬r =>
      have h_ax : ∀ x, p x := fun x =>
        Or.elim (h x)
          (fun h1 => h1)
          (fun hr => False.elim (hnr hr))
      Or.inl h_ax
    )
  )
  (fun h => Or.elim h
    (fun hx => fun x => Or.inl (hx x))
    (fun hr => fun _ => Or.inr hr)
  )

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro
  (fun h hr => fun x => (h x) hr)
  (fun h x => Or.elim (em r)
    (fun hr : r => fun _ => (h hr) x)
    (fun hnr : ¬ r => fun hr : r => False.elim (hnr hr))
  )

-- solution by Gemini
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro
  (fun h hr => fun x => (h x) hr)
  (fun h x hr => (h hr) x)


variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  let h_barbar := h barber
  let h1 : shaves barber barber → ¬ shaves barber barber := h_barbar.mp
  let h2 : ¬ shaves barber barber → shaves barber barber := h_barbar.mpr
  have hnp : ¬ shaves barber barber :=
    fun hp : shaves barber barber => h1 hp hp
  have hp : shaves barber barber := h2 hnp
  hnp hp

def even (n : Nat) : Prop := ∃ k : Nat, n = 2 * k

def prime (n : Nat) : Prop := n > 1 ∧ ∀ l m : Nat, n = l * m → (l = 1 ∨ l = n)

def infinitely_many_primes : Prop := ∀ m : Nat, ∃ n : Nat, n > m ∧ prime n

def Fermat_prime (n : Nat) : Prop := ∃ k : Nat, n = 2^(2^k) + 1 ∧ prime n

def infinitely_many_Fermat_primes : Prop := ∀ m : Nat, ∃ n : Nat, Fermat_prime n ∧ n > m

def goldbach_conjecture : Prop := ∀ k : Nat, (k ≥ 4 ∧ even k) → ∃ m n : Nat, k = m + n ∧ prime m ∧ prime n

def Goldbach's_weak_conjecture : Prop := ∀ n : Nat, (n ≥ 7 ∧ ¬ even n) → ∃ a b c : Nat, n = a + b + c ∧ prime a ∧ prime b ∧ prime c

def Fermat's_last_theorem : Prop := ∀ n : Nat, n ≥ 3 → ¬ ∃ x y z : Nat, x > 0 ∧ y > 0 ∧ z > 0 ∧ x^n + y^n = z^n
