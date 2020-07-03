variables p q r s: Prop

example (p q r : Prop) (hp : p) :
(p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) :=
by {split; try {split}; {left, assumption} <|> {right,left,assumption} <|> {right, right, assumption}}

lemma true_conclusion : q -> p -> q :=
by {intros hq hp, exact hq}

theorem and_commutes : p ∧ q -> q ∧ p :=
by {intro hpq, cases hpq with hp hq, split; assumption}

example : p ∧ q <-> q ∧ p :=
by {apply iff.intro, exact and_commutes p q, exact and_commutes q p}

theorem or_commutes : p ∨ q -> q ∨ p :=
by {intro hpq,
    apply or.elim hpq,
    intro hp, right, assumption,
    intro hq, left, assumption}

example : p ∨ q <-> q ∨ p :=
iff.intro (or_commutes p q) (or_commutes q p)

example : (p ∧ q) ∧ r <-> p ∧ (q ∧ r) :=
iff.intro
	(assume hpqr : (p ∧ q) ∧ r,
	have hr : r, from and.right hpqr,
	have hpq : p ∧ q, from and.left hpqr,
	have hp : p, from and.left hpq,
	have hq : q, from and.right hpq,
	have hqr : q ∧ r, from (|hq, hr|),
	show p ∧ (q ∧ r), from (|hp, hqr|))

	(assume hpqr : p ∧ (q ∧ r),
	show (p ∧ q) ∧ r, from (| (| (hpqr.left), ((hpqr.right).left)|) , (hpqr.right).right |))

example : (p ∨ q) ∨ r <-> p ∨ (q ∨ r) :=
iff.intro
	(assume hpqr : (p ∨ q) ∨ r,
	hpqr.elim
		(assume hpq : p ∨ q,
		hpq.elim
			(assume hp : p,
			show p ∨ (q ∨ r), from or.inl hp)

			(assume hq : q,
			suffices hqr : q ∨ r, from or.inr hqr,
			show q ∨ r, from or.inl hq))
		(assume hr : r,
		have hqr : q ∨ r, from or.inr hr,
		show p ∨ (q ∨ r), from or.inr hqr))

	(assume hpqr : p ∨ (q ∨ r),
	hpqr.elim
		(assume hp : p,
		suffices hpq : p ∨ q, from or.inl hpq,
		show p ∨ q, from or.inl hp)

		(assume hpr : q ∨ r,
		hpr.elim
			(assume hq : q,
			suffices hpq : p ∨ q, from or.inl hpq,
			show p ∨ q, from or.inr hq)

			(assume hr : r,
			show (p ∨ q) ∨ r, from or.inr hr)))

example : p ∧ (q ∨ r) <-> (p ∧ q) ∨ (p ∧ r) :=
iff.intro
	(assume hpqr : p ∧ (q ∨ r),
	have hp : p, from hpqr.left,
	have hqr : q ∨ r, from hpqr.right,
	hqr.elim
		(assume hq : q,
		suffices hpq : p ∧ q, from or.inl hpq,
		show p ∧ q, from (|hp, hq|))

		(assume hr : r,
		suffices hpr : p ∧ r, from or.inr hpr,
		show p ∧ r, from (|hp, hr|)))

	(assume hpqpr : (p ∧ q) ∨ (p ∧ r),
	hpqpr.elim
		(assume hpq : p ∧ q,
		have hp : p, from hpq.left,
		have hq : q, from hpq.right,
		suffices hqr : q ∨ r, from (|hp, hqr|),
		show q ∨ r, from or.inl hq)

		(assume hpr : p ∧ r,
		have hp : p, from hpr.left,
		have hr : r, from hpr.right,
		suffices hqr : q ∨ r, from (|hp, hqr|),
		show q ∨ r, from or.inr hr))

example : p ∨ (q ∧ r) <-> (p ∨ q) ∧ (p ∨ r) :=
by {apply iff.intro,
        intro h,
        cases h with hp hqr,
        split; {left, assumption},

        cases hqr with hq hr,
        split; {right, assumption},

        intro h,
        cases h with hpq hpr,
        apply or.elim hpq,
            intro hp,
            left, assumption,
            intro hq,
            apply or.elim hpr,
                intro hp,
                left, assumption,

                intro hr,
                right, split; assumption}

theorem implies_and : (p -> (q -> r)) <-> (p ∧ q -> r) :=
by {apply iff.intro,
        intros hpqr hpq,
        cases hpq with hp hq,
        exact (hpqr hp hq),

        intros hpqr hp hq,
        exact hpqr ⟨hp, hq⟩}

theorem implies_def : (¬ p ∨ q) -> (p -> q) :=
by {intros hnpq hp,
    cases hnpq with hnp hq,
        contradiction, assumption}

theorem or_over_implies : (p ∨ q -> r) <-> (p -> r) ∧ (q -> r) :=
by {apply iff.intro,
        intro hpqr,
        split; intro h,
            have hpq : p ∨ q, from or.inl h,
            exact hpqr hpq,

            have hpq : p ∨ q, from or.inr h,
            exact hpqr hpq,

        intros h hpq,
        cases h with hpr hqr,
        cases hpq with hp hq,
            exact hpr hp, exact hqr hq}

theorem notOr : ¬ (p ∨ q) <-> ¬ p ∧ ¬ q := or_over_implies p q false

example : ¬ (p ∧ ¬ p) :=
by {intro hpnp,
    cases hpnp with hp hnp,
    contradiction}

theorem not_implies : p ∧ ¬ q -> ¬ (p -> q) :=
by {intros h1 h2,
    cases h1 with hp hnq,
    have hnp := h2 hp,
    contradiction}

theorem false_implies : ¬ p -> (p -> q) :=
assume (hnp : ¬ p) (hp : p),
absurd hp hnp

theorem test : p ∨ false <-> p :=
by {apply iff.intro,
        intro hpf,
        cases hpf with hp f,
            exact hp, contradiction,
        intro hp,
        left, exact hp}

example : p ∧ false <-> false :=
by {apply iff.intro,
        intro hpf,
        cases hpf with hp f, contradiction,
        
        intro f, contradiction}

example : ¬ (p <-> ¬ p) :=
by {intros hpenp,
    have hpnp := hpenp.mp,
    have hnpp := hpenp.mpr,
    suffices hnp : ¬ p, from absurd (hnpp hnp) hnp,
    intro hp,
    have := (hpnp hp),
    contradiction
    }

theorem contra : (p -> q) -> (¬ q -> ¬ p) :=
by {intros hpq hnq hp,
    have hq := hpq hp,
    contradiction}

open classical

example : (p -> r ∨ s) -> ((p -> r) ∨ (p -> s)) :=
by {intro h,
    apply (em p).elim,
        intro hp,
        cases (h hp) with hr hs,
            left, exact true_conclusion p r hr,
            right, exact true_conclusion p s hs,
        intro hnp,
        left, exact false_implies p r hnp}

example : ¬ (p ∧ q) -> ¬ p ∨ ¬ q :=
by {intro hnpq,
    apply (em p).elim,
        intro hp,
        apply (em q).elim,
            intro hq,
            have hpq := and.intro hp hq,
            contradiction,

            intro hnq,
            right, exact hnq,
        intro hnp,
        left, exact hnp
}

example : ¬ (p -> q) -> p ∧ ¬ q :=
assume hnpq : ¬ (p -> q),
(em p).elim
	(assume hp : p,
	(em q).elim
		(assume hq : q,
		have hpq : p -> q, from true_conclusion p q hq,
		absurd hpq hnpq)
		(assume hnq : ¬q,
		show p ∧ ¬ q, from (|hp, hnq|)))
	(assume hnp : ¬p,
	have hpq : p -> q, from false_implies p q hnp,
	absurd hpq hnpq)

example : (p -> q) -> (¬ p ∨ q) :=
by {intro hpq,
    apply (em q).elim,
        intro hq,
        right, exact hq,

        intro hnq,
        apply (em p).elim,
            intro hp,
            have hpanq := and.intro hp hnq,
            have hpnq := not_implies p q hpanq,
            contradiction,

            intro hnp,
            left, exact hnp}

example : (¬ q -> ¬ p) -> (p -> q) :=
by {intros h hp,
    apply (em q).elim,
        intro hq, exact hq,
        intro hnq,
        have hnp := h hnq,
        contradiction}

example : p ∨ ¬ p := em p

example : ((p -> q) -> p) -> p :=
by {intro hpqp,
    apply (em p).elim,
    intro hq, exact hq,
        intro hnp,
        have hnpq : ¬ p ∨ q := or.inl hnp,
        have hpq := implies_def p q hnpq,
        have hp := hpqp hpq,
        contradiction}