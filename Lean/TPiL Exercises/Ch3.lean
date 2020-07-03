variables p q r s: Prop

lemma true_conclusion : q -> p -> q :=
assume (hq : q) (hp : p),
show q, from hq

theorem and_commutes : p ∧ q -> q ∧ p :=
assume h : p ∧ q,
show q ∧ p, from (|h.right, h.left|)

example : p ∧ q <-> q ∧ p :=
iff.intro (and_commutes p q) (and_commutes q p)

theorem or_commutes : p ∨ q -> q ∨ p :=
assume h : p ∨ q,
h.elim
	(assume hp : p,
	show q ∨ p, from or.inr hp)
	(assume hq : q,
	show q ∨ p, from or.inl hq)

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
iff.intro
	(assume hpqr : p ∨ (q ∧ r),
	hpqr.elim
		(assume hp : p,
		have hpq : p ∨ q, from or.inl hp,
		suffices hpr : p ∨ r, from (|hpq, hpr|),
		show p ∨ r, from or.inl hp)

		(assume hqr : q ∧ r,
		have hq : q, from hqr.left,
		have hr : r, from hqr.right,
		have hpq : p ∨ q, from or.inr hq,
		suffices hpr : p ∨ r, from (|hpq, hpr|),
		show p ∨ r, from or.inr hr))

	(assume hpqpr : (p ∨ q) ∧ (p ∨ r),
	have hpq : p ∨ q, from hpqpr.left,
	have hpr : p ∨ r, from hpqpr.right,
	hpq.elim
		(assume hp : p,
		show p ∨ (q ∧ r), from or.inl hp)

		(assume hq : q,
		hpr.elim
			(assume hp : p,
			show p ∨ (q ∧ r), from or.inl hp)

			(assume hr : r,
			show p ∨ (q ∧ r), from or.inr (and.intro hq hr))))

theorem implies_and : (p -> (q -> r)) <-> (p ∧ q -> r) :=
iff.intro
	(assume (hpqr : p -> q -> r) (hpq : p ∧ q),
	show r, from hpqr (hpq.left) (hpq.right))

	(assume (hpq : p ∧ q -> r) (hp : p) (hq : q),
	show r, from hpq (and.intro hp hq))

theorem implies_def : (¬ p ∨ q) -> (p -> q) :=
assume (hnpq : ¬ p ∨ q) (hp : p),
hnpq.elim
	(assume hnp : ¬ p,
	absurd hp hnp)
	(assume hq : q,
	show q, from hq)

lemma or_implies_fst : (p ∨ q -> r) -> (p -> r) :=
assume (hpqr : p ∨ q -> r) (hp : p),
have hpq : p ∨ q, from or.inl hp,
show r, from hpqr hpq

lemma or_implies_snd : (p ∨ q -> r) -> (q -> r) :=
assume (hpqr : p ∨ q -> r) (hq : q),
have hpq : p ∨ q, from or.inr hq,
show r, from hpqr hpq

theorem or_over_implies : (p ∨ q -> r) <-> (p -> r) ∧ (q -> r) :=
iff.intro
	(assume hpqr : p ∨ q -> r,
	have hpr : p -> r, from or_implies_fst p q r hpqr,
	have hqr : q -> r, from or_implies_snd p q r hpqr,
	show (p -> r) ∧ (q -> r), from (|hpr, hqr|))

	(assume (hprqr : (p -> r) ∧ (q -> r)) (hpq : p ∨ q),
	have hpr : (p -> r), from hprqr.left,
	have hqr : (q -> r), from hprqr.right,
	hpq.elim
		(assume hp : p,
		show r, from hpr hp)
		(assume hq : q,
		show r, from hqr hq))

theorem notOr : ¬ (p ∨ q) <-> ¬ p ∧ ¬ q := or_over_implies p q false

example : ¬ (p ∧ ¬ p) :=
assume hpnp : p ∧ ¬ p,
absurd (hpnp.left) (hpnp.right)

theorem not_implies : p ∧ ¬ q -> ¬ (p -> q) :=
assume (hpnq : p ∧ ¬ q) (hpq : p → q),
have hnq : ¬ q, from hpnq.right,
have hp : p, from hpnq.left,
absurd (hpq hp) hnq

theorem false_implies : ¬ p -> (p -> q) :=
assume (hnp : ¬ p) (hp : p),
absurd hp hnp

example : p ∨ false <-> p :=
iff.intro
	(assume hpf : p ∨ false,
	hpf.elim
		(assume hp : p,
		show p, from hp)
		(assume hf : false,
		false.elim hf))
	(assume hp : p,
	show p ∨ false, from or.inl hp)

example : p ∧ false <-> false :=
iff.intro
	(assume hpf : p ∧ false,
	false.elim (hpf.right))

	(assume hf : false,
	false.elim hf)

lemma not_and : (p ∧ p -> false) -> p -> false :=
assume (hnpp : ¬ (p ∧ p)) (hp : p),
have hpp : p ∧ p, from (|hp, hp|),
absurd hpp hnpp

example : ¬ (p <-> ¬ p) :=
assume hpenp : p <-> ¬ p,
have hpnp : p -> ¬ p, from hpenp.mp,
have hnpp : ¬ p -> p, from hpenp.mpr,
suffices hnp : ¬ p, from absurd (hnpp hnp) hnp,
have hppf : ¬ (p ∧ p), from (implies_and p p false).mp hpnp,
show ¬ p, from not_and p hppf

theorem contra : (p -> q) -> (¬ q -> ¬ p) :=
assume (hpq : p -> q) (hnq : ¬ q) (hp : p),
absurd (hpq hp) hnq

open classical

example : (p -> r ∨ s) -> ((p -> r) ∨ (p -> s)) :=
assume hprs : p -> r ∨ s,
(em p).elim
	(assume hp : p,
	(hprs hp).elim
		(assume hr : r,
		have hpr : p -> r, from true_conclusion p r hr,
		show ((p -> r) ∨ (p -> s)), from or.inl hpr)

		(assume hs : s,
		have hps : p -> s, from true_conclusion p s hs,
		show ((p -> r) ∨ (p -> s)), from or.inr hps))
	(assume hnp : ¬ p,
	suffices hpr : p -> r, from or.inl hpr,
	show p -> r, from false_implies p r hnp)

example : ¬ (p ∧ q) -> ¬ p ∨ ¬ q :=
assume hnpq : ¬ (p ∧ q),
(em p).elim
	(assume hp : p,
	(em q).elim
		(assume hq : q,
		absurd (and.intro hp hq) hnpq)

		(assume hnq : ¬ q,
		show ¬ p ∨ ¬ q, from or.inr hnq))
	(assume hnp : ¬ p,
	show ¬ p ∨ ¬ q, from or.inl hnp)

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
assume hpq : p -> q,
(em p).elim
	(assume hp : p,
	(em q).elim
		(assume hq : q,
		show ¬ p ∨ q, from or.inr hq)

		(assume hnq : ¬q,
		have hpnq : p ∧ ¬q, from (|hp, hnq|),
		have hnpq : ¬ (p -> q), from not_implies p q hpnq,
		absurd hpq hnpq))
	(assume hnp : ¬p,
	show ¬p ∨ q, from or.inl hnp)

example : (¬ q -> ¬ p) -> (p -> q) :=
assume (hnqnp : ¬ q -> ¬ p) (hp : p),
by_contradiction
	(assume hnq : ¬ q,
	show false, from (hnqnp hnq) hp)

example : p ∨ ¬ p := --em p
by_contradiction
	(assume hc : ¬(p ∨ ¬p),
	have hnpp : ¬p ∧ ¬¬p, from (notOr p (¬p)).mp hc,
	show false, from (hnpp.right) (hnpp.left))

example : ((p -> q) -> p) -> p :=
assume hpqp : (p -> q) -> p,
by_contradiction
	(assume hnp : ¬p,
	have hpq : p -> q, from false_implies p q hnp,
	show false, from hnp (hpqp hpq))
