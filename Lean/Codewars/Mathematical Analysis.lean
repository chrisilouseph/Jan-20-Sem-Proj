import data.real.basic data.set.intervals

/-
Mathematical Analysis
Problems by donaldsebleung
(https://www.codewars.com/collections/mathematical-analysis)
-/

open classical
attribute [instance] prop_decidable

-- Definition of the limit of a real sequence
def lim_to_inf (x : ℕ → ℝ) (l : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, abs (x n - l) < ε

/-
(Special case of a variant of Sandwich Theorem)
Given a real number l and sequences xn and yn,
if l is an upper bound of xn and a lower bound of yn
and xn - yn converges to zero,
then both xn and yn converge to l
-/
theorem exercise_1p2 (x y : ℕ → ℝ) (l : ℝ)
  (h1 : ∀ n, x n ≤ l ∧ l ≤ y n)
  (h2 : lim_to_inf (λ n, x n - y n) 0) :
  lim_to_inf x l ∧ lim_to_inf y l := by {

    split;
    
        intros e ep;
        cases h2 e ep with Nxy;
        use Nxy;
        intros n hnb;
        cases h1 n with hxl hyl;
        have hxy := le_trans hxl hyl;
        replace h := h n hnb;
        rw [sub_zero, abs_sub, abs_of_nonneg, ←sub_add_cancel (y n) l] at h,
        rw [add_sub_assoc, add_comm] at h,
        replace h := lt_sub_right_of_add_lt h,
        rw [abs_sub, abs_of_nonneg],
        have : e - (y n - l) ≤ e := by linarith,
        exact lt_of_lt_of_le h this,
        linarith, linarith,
    
    rw [add_sub_assoc] at h,
    rw [abs_of_nonneg],
    replace h := lt_sub_right_of_add_lt h,
    have : e - (l - x n) ≤ e := by linarith,
    exact lt_of_lt_of_le h this,
    linarith, linarith,
}

-- If the distance of a point from a sequence is bounded
-- by a sequence converging to zero,
-- then the former sequence converges to that point.
theorem exercise_1p3 (x y : ℕ → ℝ) (l : ℝ)
  (h₁ : ∀ n, abs (x n - l) ≤ y n) (h₂ : lim_to_inf y 0) :
  lim_to_inf x l := by {

    intros e hep,
    cases h₂ e hep with N hN,
    use N,
    intros n hnb,
    specialize hN n hnb,
    specialize h₁ n,
    have hynn := le_trans (abs_nonneg _) h₁,
    rw [sub_zero, abs_of_nonneg hynn] at hN,
    exact lt_of_le_of_lt h₁ hN
}

-- Convergence implies absolute convergence
theorem exercise_1p4 (x : ℕ → ℝ) (l : ℝ) (h₁ : lim_to_inf x l) :
  lim_to_inf (λ n, abs (x n)) (abs l) :=
begin
    intros e hep,
    cases h₁ e hep with N hn,
    use N,
    intros n hnb,
    specialize hn n hnb,
    rw abs_sub_lt_iff,
    use [lt_of_le_of_lt (sub_abs_le_abs_sub _ _) hn],
    rw abs_sub at hn,
    exact lt_of_le_of_lt (sub_abs_le_abs_sub _ _) hn
end

-- Definition of a bounded real sequence
def bounded' (x : ℕ → ℝ) :=
  ∃ B, ∀ n, abs (x n) ≤ B

-- The product of a bounded sequence and a sequence converging to zero
-- itself converges to zero
theorem exercise_1p13 (x y : ℕ → ℝ) (h₁ : lim_to_inf x 0)
  (h₂ : bounded' y) : lim_to_inf (λ n, x n * y n) 0 :=
begin
    intros e hep,
    cases h₂ with b hb,

    have hb1 : 0 < b+1,
        suffices : 0 ≤ b, linarith,
        exact le_trans (abs_nonneg _) (hb 0),

    cases h₁ (e/(b+1)) (div_pos hep hb1) with N hn,
    use N,
    intros n hnb,
    specialize hn n hnb,
    specialize hb n,
    replace hb : abs (y n) < b + 1 := lt_of_le_of_lt hb (by linarith),
    rw sub_zero at *,
    have := mul_lt_mul'' hn hb (abs_nonneg _) (abs_nonneg _),
    rwa [←abs_mul, div_mul_cancel _ (ne_of_gt hb1)] at this
end

-- Definition of continuity for a real function
def continuous_at (f : ℝ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, abs (x - a) < δ → abs (f x - f a) < ε

open set

-- Suppose f(x) is continuous at x = a and f(a) > 0. Then there is an
-- open interval containing a s.t. f(x) > 0 over the whole interval
theorem continuous_function_about_an_open_interval {f a}
  (hcont : continuous_at f a) (hgt : f a > 0) :
  ∃ b c : ℝ, a ∈ Ioo b c ∧ ∀ x ∈ Ioo b c, f x > 0 := 
begin
    rcases hcont ((f a)/2) (by linarith) with ⟨d, hdp, hc⟩,
    use [a-d,a+d],
    split,
        split; linarith,
    intros x hx,
    cases hx with hm hp,
    replace hm : a - x < d := by linarith,
    replace hp : x - a < d := by linarith,
    specialize hc x (abs_sub_lt_iff.2 ⟨hp, hm⟩),
    replace hc := sub_lt_of_abs_sub_lt_left hc,
    linarith
end

-- Definition of uniform continuity for a real function and a Lipschitz function
def uniform_continuous (f : ℝ → ℝ) :=
  ∀ ε > 0, ∃ δ > 0, ∀ x y, abs (x - y) < δ → abs (f x - f y) < ε
def lipschitz (f : ℝ → ℝ) :=
  ∃ L, ∀ x y, abs (f x - f y) ≤ L * abs (x - y)

-- All Lipschitz functions are uniform continuous
theorem uniform_continuous_of_lipschitz {f} (hf : lipschitz f) :
  uniform_continuous f :=
begin
    intros e hep,
    cases hf with l hl,

    have hlp : 0 < l+1,
        suffices : 0 ≤ l, linarith,
        have := le_trans (abs_nonneg _) (hl 1 0),
        rwa [sub_zero, abs_one, mul_one] at this,

    use [e/(l+1), div_pos hep hlp],
    intros x y h,
    specialize hl x y,
    rw lt_div_iff' hlp at h,
    
    calc abs (f x - f y)
          ≤ l * abs (x - y) + 0            : by simp only [hl, add_zero]
      ... ≤ l * abs (x - y) + abs (x - y)  : add_le_add (le_refl _) (abs_nonneg _)
      ... = (l + 1) * abs (x - y)          : by rw [add_mul, one_mul]
      ... < e                              : h
end

/-
Theorem: Given two convergent sequences, their max and min sequences converge
to the max and min of the limits respectively.

To prove this theorem, we'll first prove a series of lemmas, followed by the above:

hmax, hmin  - a characterisation of the max and min functions for real numbers
lim_add     - convergence of sum of two converging sequences
lim_scalar  - convergence of product of a converging sequence with a non-zero scalar
lim_sub     - convergence of difference of two converging sequences

We'll also use `exercise_1p4` proved earlier
-/

lemma hmax : ∀ a b : ℝ, max a b = (a + b + abs (a - b)) * (1/2) := by {
    intros,
    rw ←div_eq_mul_one_div,
    apply le_antisymm,
        apply max_le;
            apply le_div_of_mul_le (@two_pos ℝ _),
            linarith [le_abs_self (a - b)],
        linarith [le_abs_self (b - a), abs_sub a b],

    rw le_max_iff,
    cases (le_or_lt a b),
        right,
        rw [abs_sub, abs_of_nonneg];
        linarith,
    left,
    rw abs_of_pos;
    linarith
}

lemma hmin : ∀ a b : ℝ, min a b = (a + b - abs (a - b)) * (1/2) :=
    by intros a b; linarith [min_add_max a b, hmax a b]

lemma lim_add {x y l k} (hxl : lim_to_inf x l) (hyk : lim_to_inf y k) :
  lim_to_inf (λ n, (x n) + (y n)) (l + k) := by {

    intros e hep,
    cases hxl (e/2) (half_pos hep) with Nx hnx,
    cases hyk (e/2) (half_pos hep) with Ny hny,
    use max Nx Ny,
    intros n hnb,
    specialize hnx n (le_of_max_le_left hnb),
    specialize hny n (le_of_max_le_right hnb),
    rw [add_sub_comm],
    apply lt_of_le_of_lt (abs_add _ _),
    linarith
}

lemma lim_scalar {x l} (c : ℝ) (hc : c ≠ 0) (hxl : lim_to_inf x l) :
  lim_to_inf (λ n, x n * c) (l*c) := by {

    intros e hep,
    cases hxl (e/abs c) (div_pos hep (abs_pos_of_ne_zero hc)) with N hn,
    use N,
    intros n hnb,
    specialize hn n hnb,
    rw [←sub_mul, abs_mul],
    exact mul_lt_of_lt_div (abs_pos_of_ne_zero hc) hn
}

lemma lim_sub {x y l k} (hxl : lim_to_inf x l) (hyk : lim_to_inf y k) :
  lim_to_inf (λ n, (x n) - (y n)) (l - k) := by {

    have h := lim_scalar (-1) (by linarith) hyk,
    replace h := lim_add hxl h,
    rw [mul_comm, neg_one_mul, ←sub_eq_add_neg] at h,
    suffices hs : (λ (n : ℕ), x n - y n) = (λ (n : ℕ), x n + y n * -1),
        rwa hs,
    funext n,
    rw [mul_comm, neg_one_mul, ←sub_eq_add_neg]
}

lemma exercise_1p18 (x y l k) (hxl : lim_to_inf x l) (hyk : lim_to_inf y k) :
  lim_to_inf (λ n, max (x n) (y n)) (max l k) ∧
  lim_to_inf (λ n, min (x n) (y n)) (min l k) := by {
    
    have hxpy := lim_add hxl hyk,
    have hxmy := lim_sub hxl hyk,
    have ha := exercise_1p4 _ _ hxmy,
    have h2fx := lim_add hxpy ha,
    have hfx := lim_scalar (1/2) (by linarith) h2fx,
    have h2fn := lim_sub hxpy ha,
    have hfn := lim_scalar (1/2) (by linarith) h2fn,

    have hx : (λ n, max (x n) (y n)) =
      (λ (n : ℕ), (x n + y n + abs (x n - y n)) * (1 / 2)),
        funext n, rw hmax,
    
    have hn : (λ n, min (x n) (y n)) =
      (λ (n : ℕ), (x n + y n - abs (x n - y n)) * (1 / 2)),
        funext n, rw hmin,
    
    rw [hx, hn, hmax, hmin],
    exact ⟨hfx, hfn⟩
}