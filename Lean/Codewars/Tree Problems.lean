import tactic
/-
Empty Place in a Binary Tree
Problem by Brethland
(https://www.codewars.com/kata/5e030784d7721600190aa84b)
-/

-- Definition of a binary tree
inductive BTree : Type
| Leaf        : BTree
| Single_Son  : BTree -> BTree
| Binary_Sons : BTree -> BTree -> BTree

open BTree

-- Definition of functions node and empty_place by cases of the BTree argument
def node : BTree → ℕ
| Leaf                := 1
| (Single_Son t')     := 1 + node t'
| (Binary_Sons t1 t2) := 1 + node t1 + node t2

def empty_place : BTree → ℕ
| Leaf                := 2
| (Single_Son t')     := 1 + empty_place t'
| (Binary_Sons t1 t2) := empty_place t1 + empty_place t2

-- node is a non-negative function
lemma node_nonneg (t) : node t ≥ 0 := by {
    cases t with t t1 t2,
            show 1 ≥ 0,
            norm_num,
        show 1 + node t ≥ 0,
        norm_num,
    show 1 + node t1 + node t2 ≥ 0,
    norm_num
}

-- node and empty_place differ by 1
theorem l (t n) (H : node t = n) : empty_place t = n + 1 := by {
    revert n,
    induction t with t hi t1 t2 h1 h2;
        intros n H,
            change 1 = n at H,
            show 2 = n + 1,
            rw ←H,
        change 1 + node t = n at H,
        rw add_comm at H,
        have : node t = n-1,
            cases n,
                cases H,
            rw ←H,
            simp,
        replace this := hi _ this,
        show 1 + empty_place t = n + 1,
        rw [this,←H, add_comm],
        congr,
    change 1 + node t1 + node t2 = n at H,
    have : n - (1 + node t1) = node t2,
        rw [add_comm] at H,
        rw [nat.sub_eq_iff_eq_add, H],
        have := add_le_add (node_nonneg t2) (le_refl (1+node t1)),
        rwa [zero_add,H] at this,
    show empty_place t1 + empty_place t2 = _,
    have hf := h2 _ (eq.symm this),
    rw [hf, h1 (node t1) rfl, ←H],
    rw [add_comm _ (node t2)],
    rw [nat.add_sub_assoc (le_refl _), nat.sub_self, ←add_assoc],
    congr' 1,
    rw [add_comm, add_comm 1],
    congr
}