Definition nandb (a b : bool) : bool :=
match a,b with
| true, true => false
| true, false => true
| false, _ => true
end.

Definition and3 (a1 a2 a3 : bool) : bool :=
match a1, a2, a3 with
| true, true, true => true
| _, _, _ => false
end.

Fixpoint fac (n : nat) : nat :=
match n with
| O => S O
| S x => mult (S x) (fac x)
end.

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Fixpoint ltb (n m : nat) : bool := andb (leb n m) (negb (eqb n m)).

Theorem plus_id_ex : (forall n m : nat, n = m -> m = 0 -> n + m = m + 0).
Proof.
	intros.
	rewrite H.
	rewrite H0.
	simpl.
	reflexivity.
Qed.

Theorem negb_involutive : (forall b : bool, negb (negb b) = b).
Proof.
	intro b. destruct b eqn:E.
	- reflexivity.
	- reflexivity.
Qed.

Theorem andb_commutative : (forall a b : bool, andb a b = andb b a).
Proof.
	intros. destruct a, b.
		simpl. reflexivity.
		simpl. reflexivity.
		simpl. reflexivity.
		simpl. reflexivity.
Qed.

