/- Define some constants. -/

def m : Nat := 1
def n : Nat := 0
def b1 : Bool := true
def b2 : Bool := false

/- Check their types. -/
#check m
#check n
#check n + 0
#check m * (n + 0)
#check b1
#check b1 && b2
#check b1 || b2
#check true

/- Evaluate -/
#eval 5 * 4
#eval m + 2
#eval b1 && b2

#check Nat → Nat
#check Nat -> Nat
#check Nat × Nat
#check Prod Nat Nat

#check Nat → Nat → Nat
#check Nat → (Nat → Nat)
#check Nat × Nat → Nat
#check (Nat → Nat) → Nat
#check Nat.succ
#check (0, 1)
#check Nat.add
#check Nat.succ 2
#eval Nat.succ 2
#check Nat.add 3
#check Nat.add 5 2
#eval Nat.add 5 2

#check (5, 9).1
#eval (5, 9).1

#check (5, 9).2
#eval (5, 9).2

#check (5, 9, 4).2.2
#eval (5, 9, 4).2.2

def α : Type := Nat
def β : Type := Bool

#check Prod α β
#check α × β
#check Prod Nat Nat
#check Nat × Nat

def γ : Type := Nat
#check List γ
#check List Nat
#check Type
#check List
#check Prod

#check fun (x : Nat) => x + 5
#check λ (x : Nat) => x + 5
#eval (λ x : Nat => x + 5) 10

#check fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2
def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0

#check fun x : Nat => x
#check fun x : Nat => true
#check fun x => g (f x)
#eval (fun x => g (f x)) 6

#check fun (g : String → Bool) (f : Nat → String) (x : Nat) => g (f x)

#check fun (α β γ : Type) (g : β → γ) (f : α → β) (x : α) => g (f x)

def double (x : Nat) : Nat :=
  x + x

#eval double 3

def add (x : Nat) (y : Nat) :=
  x + y

def add_ (x y : Nat) :=
  x + y

#eval add 3 5
#eval add_ 3 5

def doTwice (f : Nat → Nat) (x : Nat) : Nat :=
  f (f x)

#eval doTwice double 3

def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def square (x : Nat) : Nat :=
  x * x

#eval compose Nat Nat Nat double square 3
#eval compose _ _ _ double square 3
#check compose Nat Nat Nat double

def five : Nat := 5

-- def Natural := Nat
-- def four : Natural := 4

#check let y := 5; y * y
#eval let y := 5; y * y

def twice_double (x : Nat) : Nat :=
  let y := x + x; y * y

#check twice_double
#eval twice_double 3


def foo := let a := Nat; fun x : a => x + 2
-- def bar := (fun a => fun x : a => x + 2) Nat


variable (α β γ : Type)

def compose_ (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def doTwice_ (h : α → α) (x : α) : α :=
  h (h x)

def doThrice (h : α → α) (x : α) : α :=
  h (h (h x))


#print compose_


section useful
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def compose__ := g (f x)
  def doTwice__ := h (h x)
  def doThrice_ := h (h (h x))
end useful

namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7
  def fa : Nat := f a
  def ffa : Nat := f (f a)
  #check a
  #check f
  #check fa
  #check ffa
  #check Foo.ffa
end Foo

-- #check fa
#check Foo.fa

open Foo

#check a
#check f

namespace Bar
  def a : Bool := true
end Bar

open Bar

#check Bar.a
#check a
