import tactic

/-
Squared triangular numbers
Problem by Voile
(https://www.codewars.com/kata/5d64d9c0a5aad20001b2d9f8)
-/

/- Proving that the square of the sum of first n natural numbers is equal to
the sum of the first n cubes-/

-- To add up the values of a function on natural numbers from 0 to a given n
def fsum : (ℕ → ℕ) → ℕ → ℕ :=
  λ f n, nat.rec_on n (f 0) (λ n' ihn', f (nat.succ n') + ihn')

def sq : ℕ → ℕ := λ n, n ^ 2
def cb : ℕ → ℕ := λ n, n ^ 3

-- Sum of first n natural numbers
lemma sum_nat : ∀ n, fsum id n = n * (n+1)/2 := by {
    intro n,
    induction n with n hi,
        unfold fsum,
        unfold id,
        norm_num,
    unfold fsum at *,
    unfold id at *,
    rw [hi,nat.succ_eq_add_one,add_comm],
    rw [←nat.add_mul_div_left _],
        ring,
    linarith
}

-- The product of two consecutive natural numbers is even
lemma even_cons_sum : ∀ n, 2 ∣ n * (n+1) := by {
    intro n,
    cases (nat.mod_two_eq_zero_or_one n) with h h,
        apply dvd_mul_of_dvd_left,
        exact nat.dvd_of_mod_eq_zero h,
    apply dvd_mul_of_dvd_right,
    have h1 : ¬ 2 ∣ n,
        intro h1,
        rw nat.dvd_iff_mod_eq_zero at h1,
        rw h at h1,
        norm_num at h1,
    suffices hf : ∃ k, 1 + 2 * k = n,
        cases hf with w hw,
        use w+1,
        linarith,
    have h2 : 0 < 2 := by linarith,
    use n/2,
    exact ((@nat.div_mod_unique n _ 1 (n/2) h2).1 ⟨rfl,h⟩).1,
}

-- Final Theorem
theorem nicomachus : ∀ n, sq (fsum id n) = fsum cb n := by {
    intro n,
    rw sum_nat,
    induction n with n hi,
        unfold fsum,
        unfold sq,
        unfold cb,
        norm_num,
    unfold fsum at *,
    rw ← hi,
    unfold sq,
    unfold cb,
    rw nat.pow_succ _ 2,
    repeat {rw nat.pow_two},
    rw nat.div_mul_div,
    apply nat.div_eq_of_eq_mul_right,
        norm_num,
    rw [mul_add (2*2), add_comm $ 2 * 2 * (nat.succ n * nat.succ n * nat.succ n)],
    rw [mul_assoc 2, ←mul_assoc 2 $ n * (n + 1) / 2, nat.mul_div_cancel'],
    rw [←mul_assoc 2, mul_comm 2, mul_assoc _ 2, nat.mul_div_cancel'],
    rw [nat.succ_eq_add_one],
    ring,
    repeat {apply even_cons_sum}
}

-----------------------------------------------------------

/-
A sum of consecutive odd primes is extra composite
Problem by khanh93
(https://www.codewars.com/kata/5eb0c7163c435d002f65666e)
-/

/- Proving that the sum of consecutive odd primes is extra composite,
    i.e. has atleast 3 non-trivial factors -/

universe u
open_locale classical

-- Sum of two odd numbers is even
lemma add_odds_even {a b : ℕ} : a % 2 = 1 → b % 2 = 1 → 2 ∣ a + b := by {
    intros ha hb,
    have ha1 := ((@nat.div_mod_unique a 2 1 (a/2) (by norm_num)).1 ⟨rfl,ha⟩).1,
    have hb1 := ((@nat.div_mod_unique b 2 1 (b/2) (by norm_num)).1 ⟨rfl,hb⟩).1,
    use (a/2 + b/2 + 1),
    rw [mul_add, mul_add],
    show _ = _ + _ + 1 + 1,
    rw [add_comm _ 1, add_assoc, add_comm _ 1, ←add_assoc, ha1, hb1]
}

-- All primes greater than 2 are odd
lemma prime_odd {p} : nat.prime p → p ≠ 2 → p % 2 = 1 := by {
    intros hp hnt,
    cases (nat.mod_two_eq_zero_or_one p) with h h,
        rw ←nat.dvd_iff_mod_eq_zero at h,
        cases hp with hpt hp,
        cases hp _ h with h1 h2,
            injections,
        rw h2 at hnt,
        contradiction,
    assumption
}

-- Final Theorem
theorem solution 
  {p q : ℕ} 
  (hp : nat.prime p) 
  (hq : nat.prime q) 
  (p_lt_q : p < q) 
  (p_ne_two : p ≠ 2) 
  (q_ne_two : q ≠ 2) 
  (consecutive : ∀ k, p < k → k < q → ¬ nat.prime k) : 
∃ a b c, p + q = a * b * c 
∧ a > 1 ∧ b > 1 ∧ c > 1 := 
begin
    have hae : 2 ∣ p + q :=
        add_odds_even (prime_odd hp p_ne_two) (prime_odd hq q_ne_two),

    have hab : p < (p+q)/2 ∧ (p+q)/2 < q,
        split,
            apply @lt_of_le_of_lt _ _ _ (2*p/2),
                rw [@nat.mul_div_cancel_left p 2 (by norm_num)],
            apply nat.div_lt_of_lt_mul,
            rw [nat.mul_div_cancel' hae, two_mul],
            exact nat.add_lt_add_left p_lt_q p,
        rw [@nat.div_lt_iff_lt_mul' _ _ 2 (by norm_num), mul_two],
        exact nat.add_lt_add_right p_lt_q q,

    have hac := consecutive _ hab.1 hab.2,
    unfold nat.prime at hac,
    push_neg at hac,

    have hl : 2 ≤ (p + q) / 2,
        rw @nat.le_div_iff_mul_le' _ _ 2 (by norm_num),
        show 2 + 2 ≤ _,
        apply add_le_add;
            apply nat.prime.two_le;
            assumption,
    
    cases hac,
        rw lt_iff_not_ge at hac,
        contradiction,

    rcases hac with ⟨w, hw1, hw2, hw3⟩,
    use [2, w, (p+q)/(2*w)],

    split,
        have hf : (2*w) ∣ p + q := nat.mul_dvd_of_dvd_div hae hw1,
        symmetry,
        exact nat.mul_div_cancel' hf,

    split,
        norm_num,

    have hh : ∀ n, n ≠ 0 → n ≠ 1 → n > 1,
        intros,
        cases n,
            contradiction,
        cases n,
            contradiction,
        show 0 + 1 < n.succ + 1,
        apply nat.add_lt_add_right,
        rw lt_iff_not_ge,
        exact nat.not_succ_le_zero n,

    have hwgo : w > 1,
        apply hh,
            intro hn,
            rw hn at *,
            have hn := eq_zero_of_zero_dvd hw1,
            apply hw3,
            rw hn,
        contradiction,

    use hwgo,
    apply hh;
        intro hn;
        rw [←nat.div_div_eq_div_mul,
            nat.div_eq_iff_eq_mul_right (lt_trans zero_lt_one hwgo) hw1] at hn,
        rw [@nat.div_eq_iff_eq_mul_right _ 2 _ (by norm_num) hae] at hn,
        rw [mul_zero, mul_zero, add_eq_zero_iff] at hn,
        rw [hn.1,hn.2] at p_lt_q,
        exact lt_irrefl _ p_lt_q,
    rw mul_one at hn,
    apply hw3,
    rw hn,
end