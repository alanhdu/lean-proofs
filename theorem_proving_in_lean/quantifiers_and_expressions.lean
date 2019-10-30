variables (α : Type) (p q : α → Prop)
variable r : Prop

---- Exercise 1
example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
iff.intro (
  assume hx : ∀ x, p x ∧ q x,
  have hp: ∀ x, p x, from (assume x : α, (hx x).left),
  have hq: ∀ x, q x, from (assume x: α, (hx x).right),
  ⟨hp, hq⟩
) (
  assume hpq : (∀ x, p x) ∧ (∀ x, q x),
  assume x : α,
  ⟨hpq.left x, hpq.right x⟩
)
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  assume hpq: ∀ x, p x → q x,
  assume hp: ∀ x, p x,
  assume x: α,
  have p x → q x, from hpq x,
  this (hp x)
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := 
  assume hpq : (∀ x, p x) ∨ (∀ x, q x),
  assume x : α,
  show p x ∨ q x, from (
    hpq.elim
      (assume hp: ∀ x, p x, or.inl (hp x))
      (assume hq: ∀ x, q x, or.inr (hq x))
  )

--- Exercise 2
example : α → ((∀ x : α, r) ↔ r) :=
  assume x: α,
  show (∀ x: α, r) ↔ r, from iff.intro (
    assume : ∀ x : α, r,
    this x
  ) (
    assume : r,
    assume x: α, this
  )
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
iff.intro (
  assume pxr : ∀ x, p x ∨ r,
  classical.by_cases (
    assume : r, or.inr this
  ) (
    assume nr : ¬r,
    have ∀ x, p x, from (
      assume x : α,
      or.elim (pxr x)
        (assume : p x, this)
        (assume hr: r, absurd hr nr)
    ),
    or.inl this
  )
) (
  assume : (∀ x, p x) ∨ r,
  this.elim (
    assume : ∀ x, p x,
    assume x: α, or.inl (this x)
  ) (
    assume : r,
    assume x, or.inr this
  )
)
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
iff.intro (
  assume hx : ∀ x, r → p x,
  assume hr : r,
  assume x, (hx x) hr
) (
  assume hr : r → ∀ x, p x,
  assume x, assume r,
  (hr r) x
)

--- Exercise 3
variables (men : Type) (barber : men)
variable  (shaves : men → men → Prop)

lemma contra_equiv (p : Prop) : ¬(p ↔ ¬p) :=
  assume pnp : (p ↔ ¬p),
  have np: ¬p, from (
    assume hp : p,
    have np: ¬p, from pnp.mp hp,
    np hp
  ),
  np (pnp.mpr np)
example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : false :=
  have shaves barber barber ↔ ¬shaves barber barber, from h barber,
  (contra_equiv (shaves barber barber)) this

--- Exercise 4
namespace hidden
  def divides (m n : ℕ) : Prop := ∃ k, m * k = n
  def even (n : ℕ): Prop := ∃ k, 2 * k = n
  def prime (n : ℕ) : Prop :=
    n ≥ 2 ∧ (∀ m : ℕ, (divides m n → (m = 1 ∨ m = n)))
  def infinitely_many_primes : Prop :=
    ∀ n : ℕ, ∃ m: ℕ, m > n ∧ prime m
  def Fermat_prime (n : ℕ) : Prop :=
    ∃ m : ℕ, 2^(2^m) = n ∧ prime n
  def infinitely_many_Fermat_primes : Prop :=
    ∀ n: ℕ, ∃ m: ℕ, m > n ∧ Fermat_prime n
  def goldbach_conjecture : Prop :=
    ∀ n: ℕ, (n > 2 ∧ even n) → (∃ a b, prime a ∧ prime b ∧ n = a + b)
  def Goldbach's_weak_conjecture : Prop :=
    ∀ n: ℕ,
      (n > 5 ∧ ¬even n) →
      (∃ a b c, prime a ∧ prime b ∧ prime c ∧ n = a + b + c)
  def Fermat's_last_theorem : Prop :=
    ∀ n : ℕ, n > 2 → (∀ a b c : ℕ, a^n + b^n ≠ c^n)
end hidden

--- Exercise 5
variables a : α
example : (∃ x : α, r) → r :=
  assume ⟨x, r⟩, r
example : r → (∃ x : α, r) :=
  assume r,
  ⟨a, r⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
iff.intro (
  assume : ∃ x, p x ∧ r,
  exists.elim this (
    assume x: α,
    assume : p x ∧ r,
    and.intro ⟨x, this.left⟩ this.right
  )
) (
  assume h: (∃ x, p x) ∧ r,
  have hr: r, from h.right,
  exists.elim h.left (
    assume x: α,
    assume px : p x,
    ⟨x, and.intro px hr⟩
  )
)
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
iff.intro (
  assume ⟨x, (pqx: p x ∨ q x)⟩,
  pqx.elim
    (assume : p x, or.inl ⟨x, this⟩)
    (assume : q x, or.inr ⟨x, this⟩)
) (
  assume : (∃ x, p x) ∨ (∃ x, q x),
  this.elim 
    (assume ⟨x, (px: p x)⟩, ⟨x, or.inl px⟩)
    ( assume ⟨x, (qx : q x)⟩, ⟨x, or.inr qx⟩)
)

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
iff.intro (
  assume px : ∀ x, p x,
  assume : ∃ x, ¬ p x,
  show false, from exists.elim this (
    assume x, assume : ¬p x,
    this (px x)
  )
) (
  assume npx : ¬(∃ x, ¬p x),
  assume x,
  classical.by_contradiction (
    assume : ¬p x,
    have ∃ x, ¬p x, from ⟨x, this⟩,
    npx this
  )
)

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
iff.intro (
  assume : ∃ x, p x,
  exists.elim this (
    assume x,
    assume px : p x,
    assume : ∀ x, ¬p x, (this x) px
  )
) (
  assume npx : ¬(∀ x, ¬p x),
  classical.by_contradiction (
    assume Expx : ¬∃ x, p x,
    have ∀ x, ¬p x, from (
      assume x,
      assume : p x,
      Expx ⟨x, this⟩
    ),
    npx this
  )
)
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
iff.intro (
  assume npx : ¬ ∃ x, p x,
  assume x,
  show ¬p x, from (
    assume : p x, npx ⟨x, this⟩
  )
) (
  assume npx : ∀ x, ¬ p x,
  assume : ∃ x, p x,
  show false, from exists.elim this (
    assume x,
     assume : p x, (npx x) this
  )
)
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
iff.intro (
  assume npx: ¬∀ x, p x,
  classical.by_contradiction(
    assume enpx : ¬∃ x, ¬ p x,
    have ∀ x, p x, from (
      assume x, classical.by_contradiction(
        assume : ¬p x, enpx ⟨x, this⟩
      )
    ),
    npx this
  )
) (
  assume epx: ∃ x, ¬ p x,
  assume px: ∀ x, p x,
  show false, from exists.elim epx (
    assume x,
    assume npx : ¬p x,
    npx (px x)
  )
)

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
iff.intro (
  assume pxr : ∀ x, p x → r,
  assume : ∃ x, p x,
  exists.elim this (
    assume x, pxr x
  )
) (
  assume epx : (∃ x, p x) → r,
  assume x,
  assume px,
  epx ⟨x, px⟩
)
example : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
iff.intro (
  assume ⟨x, (hx : p x → r)⟩,
  assume : ∀ x, p x,
  have p x, from this x,
  hx this
) (
  assume apxr : (∀ x, p x) → r,
  classical.by_cases (
    assume : ∀ x, p x,
    have r, from apxr this,
    ⟨a, λ a, this⟩
  ) (
    assume napx : ¬∀ x, p x,
    classical.by_contradiction (
      assume nepxr : ¬∃ x, p x → r,
      have ∀ x, p x, from (
        assume x, classical.by_contradiction (
          assume npx : ¬ p x,
          have ∃x, p x → r, from ⟨x, (assume : p x, absurd this npx)⟩,
          nepxr this
        )
      ),
      napx this
    )
  )
)
example : (∃ x, r → p x) ↔ (r → ∃ x, p x) := 
iff.intro (
  assume ⟨x, (rpx: r → p x)⟩,
  assume hr: r, ⟨x, rpx hr⟩
) (
  assume repx : r → ∃ x, p x, classical.by_cases (
    assume : r,
    have epx: ∃ x, p x, from repx this,
    exists.elim epx (
      assume x,
      assume : p x,
      ⟨x, λ r, this⟩
    )
  ) (
    assume : ¬r,
    ⟨a, assume r, absurd r this⟩
  )
)

--- Exercise 6
variables (real : Type) [ordered_ring real]
variables (log exp : real → real)
variable  log_exp_eq : ∀ x, log (exp x) = x
variable  exp_log_eq : ∀ {x}, x > 0 → exp (log x) = x
variable  exp_pos    : ∀ x, exp x > 0
variable  exp_add    : ∀ x y, exp (x + y) = exp x * exp y

-- this ensures the assumptions are available in tactic proofs
include log_exp_eq exp_log_eq exp_pos exp_add

example (x y z : real) :
  exp (x + y + z) = exp x * exp y * exp z :=
by rw [exp_add, exp_add]

example (y : real) (h : y > 0)  : exp (log y) = y :=
exp_log_eq h

theorem log_mul {x y : real} (hx : x > 0) (hy : y > 0) :
  log (x * y) = log x + log y :=
calc
  log (x * y) = log (exp (log x) * y)           : by rw exp_log_eq hx
          ... = log (exp (log x) * exp (log y)) : by rw exp_log_eq hy
          ... = log (exp (log x + log y))       : by rw exp_add (log x) (log y)
          ... = log x + log y                   : log_exp_eq (log x + log y)

--- Exercise 7
example (x : ℤ) : x * 0 = 0 :=
calc
  x * 0 = x * (1 - 1)       : by rw sub_self (1 : ℤ)
    ... = (x * 1) - (x * 1) : by rw mul_sub x 1 1
    ... = 0                 : sub_self (x * 1)