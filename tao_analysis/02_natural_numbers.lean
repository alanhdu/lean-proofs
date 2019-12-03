inductive xnat : Type
| zero : xnat
| succ : xnat → xnat
namespace xnat
  axiom succ_ne_zero : ∀ n : xnat, xnat.succ n ≠ xnat.zero
  axiom succ_inj : ∀ {n m: xnat}, xnat.succ n = xnat.succ m → n = m

  def add : xnat → xnat → xnat
  | zero m := m
  | (succ n) m := succ (add n m)

  -- Lemma 2.2.2
  theorem add_zero : ∀ {n: xnat}, add n zero = n
    | zero := by refl
    | (succ n) := begin
      have : add (succ n) zero = succ (add n zero), by refl,
      show add (succ n) zero = succ n, by rw [this, add_zero],
    end

  -- Lemma 2.2.3
  theorem add_succ : ∀ {n m : xnat}, add n (succ m) = succ (add n m) := begin
    intros n m,
    induction n, {
      refl,
    }, {
      calc
        add (succ n_a) (succ m) = succ (add n_a (succ m)) : by refl
        ...                     = succ (succ (add n_a m)) : by rw n_ih
        ...                     = succ (add (succ n_a) m): by refl
    }
  end

  theorem add_succ' : ∀ n m : xnat, add n (succ m) = succ (add n m)
  | zero m := by refl
  | (succ n) m := begin
    have h1 : add (succ n) (succ m) = succ (add n (succ m)), by refl,
    have h2 : succ (succ (add n m)) = succ (add (succ n) m), by refl,
    rw [h1, add_succ', h2]
  end


  -- Lemma 2.2.4
  theorem add_comm : ∀ n m : xnat, add n m = add m n
  | zero m := by {rw add_zero, refl}
  | (succ n) m := begin
    have : add (succ n) m = succ (add n m), by refl,
    show add (succ n) m = add m (succ n), by rw [
      this, add_comm, add_succ
     ],
  end

  -- Proposition 2.2.5
  theorem add_assoc : ∀ a b c : xnat, add a (add b c) = add (add a b) c :=
  begin
    intros a b c,
    induction a, {
      refl
    }, {
      calc
        add (succ a_a) (add b c) = succ (add a_a (add b c)) : by refl
        ...                      = succ (add (add a_a b) c) : by rw a_ih
        ...                      = add (add (succ a_a) b) c : by refl
    }
  end

  -- Proposition 2.2.6
  theorem add_left_cancel : ∀ {a b c: xnat}, add a b = add a c → b = c :=
  begin
    intros a b c,
    intro h,
    induction a, {
      calc
        b = add zero b : by refl
        ... = add zero c : h
        ... = c : by refl
    }, {
      have : add (succ a_a) b = succ (add a_a b), by refl,
      rw this at h,
      have : add (succ a_a) c = succ (add a_a c), by refl,
      rw this at h,
      have : add a_a b = add a_a c, from succ_inj h,
      from a_ih this
    }
  end

  def pos (n: xnat) : Prop := n ≠ zero

  -- Proposition 2.2.8
  theorem add_pos: ∀ a b : xnat, pos a → pos (add a b) := begin
    intros a b,
    intros pa,
    induction a, {
      have : zero = zero, by refl,
      contradiction
    }, {
      have : add (succ a_a) b = succ (add a_a b), by refl,
      rw this,
      from succ_ne_zero (add a_a b)
    }
  end

  -- colloary 2.2.9
  theorem eq_zero_of_add_eq_zero:
    ∀ {a b : xnat}, (add a b) = zero → (a = zero ∧ b = zero) :=
  begin
    intros a b h,
    induction a, {
      split,
        show zero = zero, by refl,
        show b = zero, {
          have : add zero b = b, by refl,
          rw this at h,
          assumption
        }
    }, {
      have : succ (add a_a b) = zero, from (
        calc
          succ (add a_a b) = add (succ a_a) b : by refl
          ... = zero : h
      ),
      have : succ (add a_a b) ≠ zero, from succ_ne_zero _,
      contradiction
    }
  end

  -- Lemma 2.2.10
  theorem exists_eq_succ_of_ne_zero:
    ∀ a: xnat, a ≠ zero → ∃ b: xnat, a = succ b
  | zero := by {intro, contradiction}
  | (succ a) := begin
    intro,
    existsi a, refl
  end

  theorem exists_unique_pred:
    ∀ a b c: xnat, (succ a = c) → (succ b = c) → (a = b) :=
  begin
    intros a b c sac sbc,
    have : succ a = succ b, {
      transitivity,
        assumption,
        symmetry, assumption,
    },
    show a = b, from succ_inj this
  end

  def le (n m: xnat) := ∃ a : xnat, add n a = m
  def lt (n m: xnat) := (le n m) ∧ n ≠ m

  -- Proposition 2.2.12
  theorem le_refl: ∀ n : xnat, le n n := begin
    intro n,
    existsi zero, from add_zero
  end
  theorem le_trans: ∀ {a b c : xnat}, le a b → le b c → le a c := begin
    intros a b c gab gbc,
    cases gab with n pan,
    cases gbc with m pbm,
    existsi (add n m),
    show (add a (add n m )) = c, by rw [add_assoc, pan, pbm]
  end

  lemma add_eq_zero: ∀ {n m: xnat}, add n m = n → m = zero := begin
    intros n m h,
    have : add n zero = n, from add_zero,
    have : add n m = add n zero, by {
      transitivity n, assumption,
      symmetry, assumption,
    },
    show m = zero, from add_left_cancel this
  end
  theorem le_anti_symm: ∀ {a b : xnat}, le a b → le b a → a = b := begin
    intros a b gab gba,
    cases gab with n pan, cases gba with m pbm,
    have : add n m = zero, by {
      have : a = add zero a, by refl,
      rw [←pan, ←add_assoc] at pbm,
      from add_eq_zero pbm,
    },
    have : n = zero ∧ m = zero, from eq_zero_of_add_eq_zero this,
    cases this with nz _,
    have pan: add a zero = b, by {rw ←nz, assumption},
    show a = b, {
      have : add a zero = a, from add_zero,
      rw this at pan, assumption
    }
  end

  lemma add_succ_eq_succ_add :
    ∀ {a b : xnat}, add (succ a) b = add a (succ b) := λ a b, calc
      add (succ a) b = succ (add a b) : by refl
      ...            = add a (succ b) : by {symmetry, from add_succ}

  theorem lt_succ_le: ∀ {a b : xnat}, lt a b ↔ le (succ a) b := begin
    intros a b,
    split; intro h,
    show le (succ a) b, by {
      cases h with a_le_b a_ne_b,
      cases a_le_b with n a_plus_n_eq_b,
      cases n, {
        have : a = b, from (calc
          a    = add a zero : by { symmetry, from add_zero}
          ...  = b          : a_plus_n_eq_b
        ),
        contradiction -- a ≠ b ∧ a = b
      }, {
        existsi n, from (calc
          add (succ a) n = succ (add a n) : by refl
          ...            = add a (succ n) : by rw ←add_succ
          ...            = b              : a_plus_n_eq_b
        )
      }
    },
    show lt a b, by {
      cases h with n ap1_plus_n_eq_b,
      split,
      show le a b, by {
        existsi (succ n),
        show add a (succ n) = b, {from calc
          add a (succ n) = succ (add a n) : add_succ
          ...            = add (succ a) n : by {symmetry, refl}
          ...            = b : ap1_plus_n_eq_b
        }
      },
      show a ≠ b, by {
        intro a_eq_b,
        have : add b (succ n) = b, {from calc
          add b (succ n) = add (succ b) n : by rw add_succ_eq_succ_add
          ...            = add (succ a) n : by rw a_eq_b
          ...            = b : ap1_plus_n_eq_b
        },
        have : succ n = zero, from add_eq_zero this,
        have : succ n ≠ zero, from succ_ne_zero _,
        contradiction
      },
    }
  end

  theorem lt_eq_add :
    ∀ {a b: xnat}, lt a b ↔ ∃ d: xnat, pos d ∧ b = add a d :=
  begin
    intros a b,
    split, {
      intro lt_a_b,
      have : le (succ a) b, from iff.mp lt_succ_le lt_a_b,
      cases this with n add_succ_a_n_eq_b,
      existsi (succ n),
        split,
        show pos (succ n), from succ_ne_zero n,
        show b = add a (succ n), {from calc
          b   = add (succ a) n : eq.symm add_succ_a_n_eq_b
          ... = add a (succ n) : add_succ_eq_succ_add
        }
    }, {
      intro h,
      cases h with n h1,
      cases h1 with pos_n b_eq_add_a_n,
      split,
      show le a b, by { existsi n, from eq.symm b_eq_add_a_n },
      show a ≠ b, by {
        intro a_eq_b,
        have : add b n = b, by { symmetry, rwa a_eq_b at b_eq_add_a_n},
        have : n = zero, from add_eq_zero this,
        contradiction -- n = zero, but n is positive
      }
    }
  end

  lemma lt_succ: ∀ {a b: xnat}, lt a b → lt (succ a) (succ b) := begin
    intros a b lt_a_b,
    split,
    show (le (succ a) (succ b)), by {
      cases lt_a_b.left with n _,
      existsi n, {from calc
        add (succ a) n = succ (add a n) : by refl
        ...            = succ b : by rw h
      }
    },
    show (succ a ≠ succ b), by {
      intro h,
      have: a = b, from xnat.succ_inj h,
      have: a ≠ b, from lt_a_b.right,
      contradiction
    }
  end
  theorem trichotomy: ∀ {a b: xnat}, lt a b ∨ a = b ∨ lt b a
  | zero zero := or.inr (or.inl (eq.refl zero))
  | (succ a) zero := begin
    right, right, show lt zero (succ a), by {
      split,
      show le zero (succ a), by { existsi (succ a), refl },
      show zero ≠ succ a, by trivial
    },
  end
  | zero (succ b) := begin
    left,
    show lt zero (succ b), by {
      split,
      show le zero (succ b), by { existsi (succ b), refl },
      show zero ≠ succ b, by trivial
    }
  end
  | (succ a) (succ b) := begin
    have : lt a b ∨ a = b ∨ lt b a, from trichotomy,
    cases this with lt_a_b h,
    any_goals { cases h with a_eq_b lt_b_a }, {
      -- a < b
      left, from lt_succ lt_a_b,
    }, {
      -- a = b
      right, left,
      show succ a = succ b, by rw a_eq_b,
    }, {
      -- a > b
      right, right, from lt_succ lt_b_a,
    }
  end
end xnat


example : 4 ≠ 0 := nat.succ_ne_zero 3

example : 6 ≠ 2 := begin
  intro h,
  have : 5 = 1, from nat.succ_inj h,
  have : 4 = 0, from nat.succ_inj this,
  have : 4 ≠ 0, from nat.succ_ne_zero 3,
  contradiction
end
