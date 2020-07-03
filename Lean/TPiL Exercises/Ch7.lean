import data.nat.basic
universe u

namespace hidden
-- BEGIN
inductive list (α : Type u)
| nil {} : list
| cons : α → list → list

namespace list

variable {α : Type}

notation h :: t  := cons h t

def append (s t : list α) : list α := list.rec t (λ x l u, x::u) s
def length (s : list α) : ℕ := list.rec 0 (λ h t l, 1 + l) s

notation s ++ t := append s t
def reverse (s : list α) : list α :=
list.rec_on s nil (λ h t l, l ++ h::nil)

theorem nil_append (t : list α) : nil ++ t = t := rfl

theorem cons_append (x : α) (s t : list α) :
  x::s ++ t = x::(s ++ t) := rfl

theorem cons_nil_append (x : α) (t : list α) :
  x::t = x :: nil ++ t := rfl

theorem append_nil (t : list α) : t ++ nil = t :=
list.rec rfl (λ h e hi, by rw [cons_append,hi]) t

theorem append_assoc (r s t : list α) :
  r ++ s ++ t = r ++ (s ++ t) :=
list.rec_on r
    (by rw [nil_append, nil_append])
(λ f l hi, by rw[cons_append,cons_append,hi,cons_append])

theorem nil_length : length (@nil α) = 0 := rfl
theorem cons_length (h : α) (t : list α) :
  length (h::t) = 1 + length t := rfl

theorem append_length (r s : list α) :
  length (r ++ s) = length r + length s :=
list.rec_on r
  (by rw [nil_append, nil_length,zero_add])
(λ h t hi, by rw [cons_length, cons_append, cons_length, hi, add_assoc])

theorem nil_reverse : reverse (@ nil α) = nil := rfl
theorem cons_reverse (h : α) (t : list α) :
  reverse (h::t) = reverse t ++ (h::nil) := rfl
theorem append_reverse (r s : list α) :
  reverse (r ++ s) = reverse s ++ reverse r :=
list.rec_on r
  (by rw [nil_reverse, append_nil, nil_append])
(λ h t hi, by rw [cons_append, cons_reverse, cons_reverse, hi, append_assoc])

theorem reverse_idem (s : list α) : reverse (reverse s) = s :=
list.rec_on s rfl
(λ h t hi, by rw [cons_reverse, append_reverse, hi, cons_reverse];
              rw [nil_reverse, nil_append, ←cons_nil_append])

theorem length_reverse (s : list α) : length (reverse s) = length s :=
list.rec_on s (by rw nil_reverse)
(λ h t hi, by rw [cons_reverse, append_length, hi, cons_length];
              rw [cons_length, nil_length, add_zero, add_comm])

end list
-- END
end hidden

mutual inductive even, odd
with even : ℕ → Prop
| even_zero : even 0
| even_succ : ∀ n, odd n → even (n + 1)
with odd : ℕ → Prop
| odd_succ : ∀ n, even n → odd (n + 1)

inductive par : ℕ → ℤ → Prop
| even_zero : par 0 0
| even_succ : ∀ n, par 0 n → par 1 (n + 1)
| even_pred : ∀ n, par 0 n → par 1 (n - 1)
| odd_succ : ∀ n, par 1 n → par 0 (n + 1)
| odd_pred : ∀ n, par 1 n → par 0 (n - 1)
