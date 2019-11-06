section  -- Propositions and Proofs
  variables p q r s : Prop

  -- commutativity of ∧ and ∨
  example : p ∧ q ↔ q ∧ p :=
  begin
    split;
    intro h;
    cases h with hl hr;
    exact and.intro hr hl
  end

  example : p ∨ q ↔ q ∨ p :=
  begin
    apply iff.intro;
    intro h;
    cases h with hl hl;
    { right, exact hl } <|> { left, exact hl }
  end

  -- associativity of ∧ and ∨
  example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  begin
    apply iff.intro;
    intro h;
    repeat { split },
    all_goals {
      cases h with h_left h_right,
      cases h_left with hp hq <|> cases h_right with hq hr,
      assumption
    }
  end

  example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  begin
    split;
    intro h, {
      cases h with h1 h2,
      cases h1 with hp hq,
      all_goals {
        repeat { { left, assumption} <|> right <|> assumption }
      }
    }, {
      cases h with h1 h1,
      { left, left, assumption },
      cases h1 with hq hr,
      try { left }, all_goals { right, assumption },
    }
  end

  -- distributivity
  example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  begin
    split; intro h, {
      cases h.right,
      left, exact and.intro h.left h_1,
      right, exact and.intro h.left h_1,
    }, {
      cases h;
      split; cases h,
      all_goals { assumption <|> {left, assumption} <|> {right, assumption }}
    },
  end
  example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  begin
    split; intro h, {
      cases h;
      split,
      any_goals { {left, assumption} },
      all_goals { right },
      exact h.left, exact h.right
    }, {
      cases h,
      cases h_left;
      cases h_right,
      any_goals { left, assumption },
      right, exact and.intro h_left h_right,
    }
  end

  -- other properties
  example : (p → (q → r)) ↔ (p ∧ q → r) :=
  begin
    split; intro h,
    {
      intro pq,
      show r, from (h (pq.left)) pq.right,
    }, {
      intro p, intro q,
      exact h ⟨p, q⟩
    }
  end

  example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  begin
    split; intro h, {
      split; intro h1,
        exact h (or.inl h1),
        exact h (or.inr h1),
    }, {
      intro pq,
      cases pq,
        exact h.left pq,
        exact h.right pq,
    }
  end

  example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  begin
    split; intro h, {
      split; intro n,
        have : p ∨ q, from or.inl n, contradiction,
        have : p ∨ q, from or.inr n, contradiction,
    }, {
      intro n, cases n,
        have : ¬p, from h.left, contradiction,
        have : ¬q, from h.right, contradiction,
    }
  end
  example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  begin
    intro h,
    intro pq,
    have : p, from pq.left,
    have : q, from pq.right,
    cases h; contradiction
  end

  example : ¬(p ∧ ¬p) :=
  begin
    intro h,
    cases h, contradiction
  end

  example : p ∧ ¬q → ¬(p → q) :=
  begin
    intro h,
    cases h with hl hr,
    intro pq,
    have : q, from pq hl,
    contradiction 
  end

  example : ¬p → (p → q) :=
  begin
    repeat { intro },
    contradiction
  end

  example : (¬p ∨ q) → (p → q) :=
  begin
    repeat { intro },
    cases a,
    contradiction,
    assumption
  end

  example : p ∨ false ↔ p :=
  begin
    split; intro h, {
      cases h,
        assumption,
        contradiction
    }, {
      exact or.inl h
    }
  end

  example : p ∧ false ↔ false :=
  begin
    split; intro h,
    cases h,
    all_goals { contradiction }
  end

  example : ¬(p ↔ ¬p) :=
  begin
    intro h,
    cases h,
    have : p → false, {
      intro hp,
      have : ¬p, from h_mp hp,
      contradiction
    },
    have : p, from h_mpr this,
    have : ¬p, from h_mp this,
    contradiction
  end

  example : (p → q) → (¬q → ¬p) :=
  begin
    repeat { intro },
    have : q, from a a_2,
    contradiction
  end

  -- these require classical reasoning
  example : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
  begin
    intro h,
    cases classical.em r, {
      have : p → r, { intro , assumption },
      left, assumption,
    }, {
      have : p → s, {
        intro,
        have : r ∨ s, from h a,
        cases this, contradiction, assumption
      },
      right, assumption
    }
  end

  example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  begin
    intro h,
    cases classical.em p, {
      have : ¬q, {
        intro,
        have : p ∧ q, from and.intro h_1 a,
        contradiction
      },
      exact or.inr this
    }, {
      left, assumption
    }
  end

  example : ¬(p → q) → p ∧ ¬q :=
  begin
    intro h,
    split, {
      from classical.by_contradiction 
        begin
          repeat { intro },
          have : p → q, {
            intro h, contradiction,
          },
          contradiction
        end
    }, {
      intro,
      have : p → q, intro, assumption,
      contradiction,
    }
  end

  example : (p → q) → (¬p ∨ q) :=
  begin
    intro h,
    cases classical.em p,
      right, from h h_1,
      left, assumption
  end

  example : (¬q → ¬p) → (p → q) :=
  begin
    repeat { intro },
    from classical.by_contradiction
      begin
        intro nq,
        have : ¬p, from a nq,
        contradiction
      end
  end

  example : p ∨ ¬p := classical.em p

  example : (((p → q) → p) → p) :=
  begin
    intro,
    cases classical.em p,
      { assumption },
      { have : p → q, intro, contradiction,
        from a this,
      }
  end
end

------ Quantifiers and Expressions
section  -- 4.1
  variables (α : Type) (p q : α → Prop)

  example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  begin
    split; intro h, {
      split; intro x,
      from (h x).left,
      from (h x).right,
    }, {
      cases h,
      intro x,
      split, from h_left x, from h_right x,
    }
  end

  example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  begin
    intros h h₁ x,
    have : p x, from h₁ x,
    from (h x) this
  end

  example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  begin
    intros h x,
    cases h,
      { left, from h x },
      { right, from h x },
  end
end

section -- 4.2
  variables (α : Type) (p q : α → Prop)
  variable r : Prop

  example : α → ((∀ x : α, r) ↔ r) :=
  begin
    intro α,
    split; intro h,
      { from h α },
      { intro, from h }
  end
  example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  begin
    split; intro h, {
      apply classical.by_cases,
        intro, right, assumption,
        intro nr, left, intro x, cases h x,
          assumption,
          contradiction
    }, {
      intro x,
      cases h,
        left, from h x,
        right, assumption
    }
  end

  example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  begin
    split;
    intros h h₁ h₂;
    from h h₂ h₁
  end
end

section -- 4.3
  variables (men : Type) (barber : men)
  variable  (shaves : men → men → Prop)

  example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : false :=
  begin
    have shave_barber, from h barber,
    have : ∀ p: Prop, (p ↔ ¬p) → false, {
      intros p h,
      cases h,
      have : ¬p, { 
        intro hp, 
        have : ¬p, from h_mp hp,
        contradiction
      },
      have : p, from h_mpr this,
      contradiction
    }, 
    from (this (shaves barber barber)) shave_barber
  end
end

section -- 4.5
  variables (α : Type) (p q : α → Prop)
  variable a : α
  variable r : Prop
  
  example : (∃ x : α, r) → r :=
  begin
    intro h,
    cases h with x hr,
    from hr
  end
  
  include a
  example : r → (∃ x : α, r) :=
  begin
    intro hr, split; assumption
  end
  example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := 
  begin
    split; intro h, {
      cases h with x pr,
      cases pr,
      repeat { split },
      all_goals { assumption }
    }, {
      cases h, cases h_left,
      repeat { split },
      all_goals { assumption },
    }
  end
  
  example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  begin
    split; intro h, {
      cases h with x pq,
      cases pq,
        { left, split; assumption },
        { right, split; assumption },
    }, {
      cases h; cases h with x h;
      split,
        { left, from h },
        { right, from h },
    }
  end
  
  example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  begin
    split; intro h, {
      intro ex,
      cases ex with x np,
      have : p x, from h x,
      contradiction
    }, {
      intro x,
      from classical.by_contradiction
        (by { intro np, from h ⟨x, np⟩ })
    }
  end
  
  example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  begin
    split; intro h, {
      intro apx, 
      cases h with x px,
      have : ¬p x, from apx x,
      contradiction
    }, {
      from classical.by_contradiction
      begin
        intro epx,
        have : ∀ x, ¬p x, {
          intros x px,
          from epx ⟨x, px⟩
        },
        contradiction
      end
    }
  end
  
  example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  begin
    split; intro h, {
      intros x px, from h ⟨x, px⟩
    }, { 
      intro ex,
      cases ex with x px,
      have : ¬p x, from h x,
      contradiction
    }
  end
  
  example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  begin
    split; intro h, {
      from classical.by_contradiction
      begin
        intro ex,
        have : ∀ x, p x, {
          intro x,
          from classical.by_contradiction 
            ( by { intro npx, from ex ⟨x, npx⟩})
        },
        contradiction
      end
    }, {
      cases h with x npx,
      intros apx,
      have : p x, from apx x,
      contradiction
    }
  end
  
  example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  begin
    split; intro h, {
      intro epx,
      cases epx with x px,
      from (h x) px
    }, {
      intros x px,
      from h ⟨x, px⟩
    }
  end
  
  example : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  begin
    split; intro h, {
      intro apx,
      cases h with x pxr,
      from pxr (apx x)
    }, {
      apply classical.by_cases, {
        intro hapx,
        have : r, from h hapx,
        existsi a, intro, assumption
      }, {
        intro napx,
        have : ∃x, ¬p x, apply classical.by_contradiction, {
          intro nepx,
          have : ∀ x, p x, {
            intro x,
            apply classical.by_contradiction,
            intro npx,
            have : ∃x, ¬p x, from exists.intro x npx,
            contradiction
          },
          contradiction
        },
        cases this with x npx,
        existsi x,
        intro, contradiction
      }
    }
  end
  
  example : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  begin
    split; intro h, {
      intro hr,
      cases h with x rpx,
      existsi x, from rpx hr,
    }, {
      apply classical.by_cases, {
        intro hr,
        cases (h hr) with x px,
        existsi x, intro, assumption,
      }, {
        intro hr,
        existsi a, intro, contradiction,
      }
    }
  end
end

section -- 4.6
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
    begin
      rw [←(exp_log_eq hx), ←(exp_log_eq hy)],
      rw ←exp_add,
      repeat { rw log_exp_eq },
    end
end

section -- 4.7
  example (x : ℤ) : x * 0 = 0 :=
  begin
    simp
  end
end

section -- 5.8
  example (p q r : Prop) (hp : p) :
  (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) :=
  by { repeat { split }, repeat { {left, assumption} <|> right <|> assumption } }
end