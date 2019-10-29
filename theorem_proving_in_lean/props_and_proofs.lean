variables p q r s : Prop

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  iff.intro (
  assume h : p ∧ q,
  show q ∧ p, from ⟨h.right, h.left⟩
  ) (
  assume h : q ∧ p,
  show p ∧ q, from ⟨h.right, h.left⟩
  )
example : p ∨ q ↔ q ∨ p :=
  iff.intro (
    assume h: p ∨ q,
    show q ∨ p, from h.elim or.inr or.inl
  ) (
    λ (h : q ∨ p), h.elim
      (assume hq: q, show p ∨ q, from or.inr hq)
      (assume hp: p, show p ∨ q, from or.inl hp)
  )

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  iff.intro (
    assume h: (p ∧ q) ∧ r,
    show p ∧ (q ∧ r), from ⟨ h.left.left, ⟨h.left.right , h.right⟩ ⟩
  ) (
    assume h: p ∧ (q ∧ r),
    show (p ∧ q) ∧ r, from ⟨⟨h.left, h.right.left⟩ , h.right.right⟩ 
  )
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  iff.intro (
    assume h: (p ∨ q) ∨ r,
    show p ∨ (q ∨ r), from h.elim 
      (λ (hpq: p ∨ q), hpq.elim or.inl (λ hq: q, or.inr (or.inl hq)))
      (λ (hr: r), or.inr (or.inr hr))
  ) (
    assume h: p ∨ (q ∨ r),
    show (p ∨ q) ∨ r, from h.elim
      (assume hp: p, or.inl (or.inl hp))
      (assume hqr: q ∨ r, hqr.elim
        (assume hq: q, or.inl (or.inr hq))
        or.inr
      )
  )

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  iff.intro (
    assume h: p ∧ (q ∨ r),
    h.right.elim 
      (assume hq: q, or.inl ⟨h.left, hq⟩)
      (assume hr: r, or.inr ⟨h.left, hr⟩)
  ) (
    assume h: (p ∧ q) ∨ (p ∧ r),
    h.elim
      (assume hpq: p ∧ q, ⟨hpq.left, or.inl hpq.right⟩)
    (assume hpr: p ∧ r, ⟨hpr.left, or.inr hpr.right⟩)
)
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  iff.intro (
    assume h: p ∨ (q ∧ r),
    h.elim
      (assume hp: p, ⟨ or.inl hp, or.inl hp ⟩)
      (assume hqr: q ∧ r, ⟨ or.inr hqr.left, or.inr hqr.right ⟩)
  ) (
    assume h: (p ∨ q) ∧ (p ∨ r),
    h.left.elim
      or.inl
      (assume hq: q, h.right.elim
        or.inl
        (assume hr: r, or.inr ⟨hq, hr⟩ )
      )
  )

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  iff.intro (
    assume hpqr: p → (q → r),
    assume hpq: p ∧ q,
    (hpqr hpq.left) hpq.right
  ) (
    assume hpqr: (p ∧ q) → r,
    assume hp: p,
    assume hq: q,
    hpqr (⟨ hp, hq ⟩)
  )
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  iff.intro (
    assume hpqr: (p ∨ q) → r,
    ⟨
      assume hp: p, show r, from hpqr (or.inl hp),
      assume hq: q, show r, from hpqr (or.inr hq)
    ⟩
  ) (
    assume hpqr: (p → r) ∧ (q → r),
    assume hpq: p ∨ q,
    hpq.elim
      (assume hp: p, hpqr.left hp)
      (assume hq: q, hpqr.right hq)
  )
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  iff.intro (
    assume npq: ¬(p ∨ q), ⟨
      assume p, show false, from npq (or.inl p),
      assume q, show false, from npq (or.inr q),
    ⟩
  ) (
    assume npq: ¬p ∧ ¬q,
    assume hpq: p ∨ q,
    hpq.elim npq.left npq.right
  )
example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  assume hpq: ¬p ∨ ¬q,
  assume pq: p ∧ q,
  hpq.elim
    (assume np: ¬p, np pq.left)
    (assume nq: ¬q, nq pq.right)
example : ¬(p ∧ ¬p) :=
  assume hp: p ∧ ¬p, hp.right hp.left
example : p ∧ ¬q → ¬(p → q) :=
  assume npq: p ∧ ¬q,
  assume hpq: p → q,
  npq.right (hpq npq.left)
example : ¬p → (p → q) :=
  assume np: ¬p,
  assume hp: p,
  absurd hp np
example : (¬p ∨ q) → (p → q) :=
  assume hpq: ¬p ∨ q,
  assume hp: p,
  hpq.elim
    (assume np: ¬p, absurd hp np)
    (assume hq: q, hq)
example : p ∨ false ↔ p :=
  iff.intro (
    assume hpn: p ∨ false,
    hpn.elim id false.elim
  ) (
    or.inl
  )
example : p ∧ false ↔ false :=
  iff.intro and.right false.elim
example : ¬(p ↔ ¬p) :=
  assume pnp: p ↔ ¬p,
  have pf: p → false, from (
    assume hp: p, (pnp.mp hp) hp
  ),
  have hp: p, from pnp.mpr pf,
  pf hp
example : (p → q) → (¬q → ¬p) :=
  assume hpq: p → q,
  assume nq: ¬q,
  assume hp: p,
  nq (hpq hp)

-- these require classical reasoning
example : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
  assume prs: p → r ∨ s,
  (classical.em r).elim
    (assume hr: r, or.inl (assume hp: p, hr))
    (assume nr: ¬r, or.inr (
      assume hp: p,
      have rs: r ∨ s, from prs hp,
      show s, from (rs.elim (assume hr: r, absurd hr nr) (assume hs, hs))
    ))
example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  assume npq: ¬(p ∧ q),
  (classical.em p).elim (
    assume hp: p,
    have nq: ¬q, from (assume hq: q, npq ⟨hp, hq⟩),
    or.inr nq
  ) (
    or.inl
  )
example : ¬(p → q) → p ∧ ¬q :=
  assume npq: ¬(p → q),
  (classical.em p).elim (
    assume hp: p,
    have nq: ¬q, from (assume hq: q, npq (λ _, hq)),
    and.intro hp nq
  ) (
    assume np: ¬p,
    have pq: p → q, from (assume hp: p, absurd hp np),
    absurd pq npq
  )
example : (p → q) → (¬p ∨ q) :=
  assume hpq: p → q,
  (classical.em p).elim (
    assume hp: p,
    have hq: q, from hpq hp,
    or.inr hq
  ) (
    or.inl
  )
example : (¬q → ¬p) → (p → q) :=
  assume nqp: ¬q → ¬p,
  assume hp: p,
  classical.by_contradiction (
    assume nq: ¬q,
    (nqp nq) hp
  )
example : p ∨ ¬p := classical.em p
example : (((p → q) → p) → p) :=
  assume pqp: (p → q) → p,
  classical.by_contradiction (
    assume np: ¬p,
    have pq: (p → q), from (assume hp: p, absurd hp np),
    have hp: p, from pqp pq,
    np hp
  )