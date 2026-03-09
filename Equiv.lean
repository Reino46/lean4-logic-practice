variable (p q r : Prop)

-- αντιμεταθετικοτητα των ∧ και ∨ :
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q =>
      have hp : p := h.left
      have hq : q := h.right
      show q ∧ p from ⟨hq, hp⟩)
    (fun h : q ∧ p =>
      have hq : q := h.left
      have hp : p := h.right
      show p ∧ q from ⟨hp, hq⟩)

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h : p ∨ q =>
      Or.elim h
      (fun hp : p =>
        show q ∨ p from Or.inr hp)
      (fun hq : q =>
        show q ∨ p from Or.inl hq))
    (fun h : q ∨ p =>
      Or.elim h
      (fun hq : q =>
        show p ∨ q from Or.inr hq)
      (fun hp : p =>
        show p ∨ q from Or.inl hp))

-- προσεταιριστικοτητα
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun h : (p ∧ q) ∧ r =>
      have hpq : p ∧ q := h.left
        have hp : p := hpq.left
        have hq : q := hpq.right
      have hr : r := h.right
      show p ∧ (q ∧ r) from ⟨hp, ⟨hq, hr⟩⟩)
    (fun h : p ∧ (q ∧ r) =>
      have hp : p := h.left
      have hqr : q ∧ r := h.right
        have hq : q := hqr.left
        have hr : r :=hqr.right
      show (p ∧ q) ∧ r from ⟨⟨hp, hq⟩, hr⟩)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun h : (p ∨ q) ∨ r =>
      Or.elim h
        (fun hpq : p ∨ q =>
          Or.elim hpq
            (fun hp : p =>
              show p ∨ (q ∨ r) from Or.inl hp)
            (fun hq : q =>
              show p ∨ (q ∨ r) from Or.inr (Or.inl hq)))
        (fun hr : r =>
          show p ∨ (q ∨ r) from Or.inr (Or.inr hr)))
    (fun h : p ∨ (q ∨ r) =>
      Or.elim h
        (fun hp : p =>
          show (p ∨ q) ∨ r from Or.inl (Or.inl hp))
        (fun hqr : q ∨ r =>
          Or.elim hqr
            (fun hq : q =>
              show (p ∨ q) ∨ r from Or.inl (Or.inr hq))
            (fun hr : r =>
              show (p ∨ q) ∨ r from Or.inr hr)))

-- επιμεριστικοτητα
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h : p ∧ (q ∨ r) =>
      have hp : p := h.left
      have hqr : q ∨ r := h.right
      Or.elim hqr
        (fun hq : q =>
            show (p ∧ q) ∨ (p ∧ r) from Or.inl ⟨hp, hq⟩)
        (fun hr : r =>
            show (p ∧ q) ∨ (p ∧ r) from Or.inr ⟨hp, hr⟩))
    (fun h : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim h
        (fun hpq : p ∧ q =>
          have hp : p := hpq.left
          have hq : q := hpq.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inl hq⟩)
        (fun hpr : p ∧ r =>
          have hp : p := hpr.left
          have hr : r := hpr.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inr hr⟩))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (fun h : p ∨ (q ∧ r) =>
      Or.elim h
        (fun hp : p =>
          show (p ∨ q) ∧ (p ∨ r) from ⟨Or.inl hp, Or.inl hp⟩)
        (fun hqr : q ∧ r =>
          have hq : q := hqr.left
          have hr : r := hqr.right
          show (p ∨ q) ∧ (p ∨ r) from ⟨Or.inr hq, Or.inr hr⟩))
    (fun h : (p ∨ q) ∧ (p ∨ r) =>
      have hpq : p ∨ q := h.left
      Or.elim hpq
        (fun hp : p =>
          show p ∨ (q ∧ r) from Or.inl hp)
        (fun hq : q =>
          have hpr : p ∨ r := h.right
          Or.elim hpr
            (fun hp2 : p =>
              show p ∨ (q ∧ r) from Or.inl hp2)
            (fun hr : r =>
              show p ∨ (q ∧ r) from Or.inr ⟨hq, hr⟩)))

-- αλλες ιδιοτητες
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (fun h : p → (q → r) =>
      fun hpq : p ∧ q =>
        have hp : p := hpq.left
        have hq : q := hpq.right
        show r from h hp hq)
    (fun h : p ∧ q → r =>
      fun hp : p =>
      fun hq : q =>
      show r from h ⟨hp, hq⟩)

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (fun h : (p ∨ q) → r =>
      show (p → r) ∧ (q → r) from And.intro (
        fun hp : p =>
          show r from h (Or.inl hp)
      ) (
        fun hq : q =>
          show r from h (Or.inr hq)
      )
    )
    (fun h : (p → r) ∧ (q → r) =>
      have hpr : p → r := h.left
      have hqr : q → r := h.right
      fun hpq : p ∨ q =>
        show r from Or.elim hpq hpr hqr
    )

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (fun hnpq : p ∨ q → False =>
      show ¬p ∧ ¬q from And.intro (
        fun hp : p =>
          show False from hnpq (Or.inl hp)
      ) (
        fun hq : q =>
          show False from hnpq (Or.inr hq)
      )
    )
    (fun hnpnq : ¬p ∧ ¬q =>
      have hnp : ¬p := hnpnq.left
      have hnq : ¬q := hnpnq.right
      fun hpq : p ∨ q =>
        show False from Or.elim hpq hnp hnq)
