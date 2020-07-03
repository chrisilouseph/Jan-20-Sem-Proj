Theorem absurd1 : (forall Q : Prop, False -> Q).
Proof.
	intros.
	case H.
Qed.

Theorem not_not : (forall A : Prop, A -> ~~A).
Proof.
	intros.
	unfold not.
	intros.
	exact (H0 H).
Qed.

Theorem contraposition : (forall A B : Prop, (A -> B) -> (~B -> ~A)).
Proof.
	unfold not.
	intros.
	exact (H0 (H H1)).
Qed.


Theorem True_is_provable : True.
Proof.
  exact I.
Qed.

Theorem False_unprovable : ~False.
Proof.
  intros proofFalse.
  case proofFalse.
Qed.

Theorem funda_Implication : ~(True -> False).
Proof.
  intros TImpF.
  refine (TImpF _).
    exact I.
Qed.

Theorem not_true_is_false : (forall b : bool, b <> true -> b = false).
Proof.
	unfold not.
	intros [] H.
	
		apply absurd1.
		apply H.
		reflexivity.
		
		reflexivity.
Qed.

Theorem absurd2 : (forall A C : Prop, A -> ~ A -> C).
Proof.
  intros A C.
  intros proofA proofNA.
  unfold not in proofNA.
  case proofNA.
  exact proofA.
Qed.

Require Import Bool.

Theorem true_is_True : Is_true true.
Proof.
  simpl.
  exact I.
Qed.

Theorem not_eqb_true_false : ~(Is_true (eqb true false)).
Proof.
  simpl.
  exact False_unprovable.
Qed.

Theorem eqb_a_a : (forall a : bool, Is_true (eqb a a)).
Proof.
  intros a.
  case a.

    simpl.
    exact I.

    simpl.
    exact I.

Qed.

Theorem thm_eqb_a_t: (forall a:bool, (Is_true (eqb a true)) -> (Is_true a)).
Proof.
  intros a.
  case a.

    simpl.
    intros T.
    exact I.

    simpl.
    intros F.
    case F.
Qed.

Theorem left_or : (forall A B : Prop, A -> A \/ B).
Proof.
	intros A B.
	intros proofA.
	pose (proofAorB := or_introl proofA : A \/ B).
	exact proofAorB.
Qed.

Theorem right_or : (forall A B : Prop, B -> A \/ B).
Proof.
	intros A B.
	intros proofB.
	refine (or_intror _).
		exact proofB.
Qed.

Theorem or_commutes : (forall A B: Prop, A \/ B -> B \/ A).
Proof.
	intros A B.
	intros proofAorB.
	destruct proofAorB as [proofA | proofB].
	
		exact (or_intror proofA).
		
		exact (or_introl proofB).
Qed.

Theorem or_indemp : (forall A : Prop, A \/ A -> A).
Proof.
	intros A.
	intros AorA.
	case AorA.
	
		intros proofA.
		exact proofA.
		
		intros proofA.
		exact proofA.
Qed.

Theorem both_and : (forall A B : Prop, A -> B -> A /\ B).
Proof.
	intros A B.
	intros proofA proofB.
	exact (conj proofA proofB).
Qed.

Theorem and_commutes : (forall A B: Prop, A /\ B -> B /\ A).
Proof.
	intros A B.
	intros AandB.
	destruct AandB as [ proofA proofB ].
	exact (conj proofB proofA).
Qed.

Theorem and_indemp : (forall A : Prop, A /\ A -> A).
Proof.
	intros A.
	intros AandA.
	destruct AandA as [ x y ].
	exact x.
Qed.

Theorem orb_is_or : (forall a b, Is_true (orb a b) <-> Is_true a \/ Is_true b).
Proof.
	intros.
	unfold iff.
	refine (conj _ _).
	
		intros.
		case a, b.

			simpl.
			exact (or_introl I).
			
			simpl.
			exact (or_introl I).
			
			simpl.
			exact (or_intror I).
			
			simpl in H.
			case H.
					
		intro.
		case a, b.
		
			simpl.
			exact I.
		
			simpl.
			exact I.
		
			simpl.
			exact I.
			
			simpl.
			simpl in H.
			case H.
			
				intro.
				case H0.
				
				intro.
				case H0.
Qed.

Theorem andb_is_and : (forall a b, Is_true (andb a b) <-> Is_true a /\ Is_true b).
Proof.
	intros.
	unfold iff.
	refine (conj _ _).
	
		intros.
		case a, b.
		
			simpl.
			exact (conj I I).
			
			simpl in H.
			case H.
			
			simpl in H.
			case H.
			
			simpl in H.
			case H.
			
		intros.
		case a, b.
		
			simpl.
			exact I.
			
			simpl in H.
			destruct H.
			case H0.
			
			simpl in H.
			destruct H.
			case H.
			
			simpl in H.
			destruct H.
			case H0.
Qed.

Theorem negb_is_not : (forall a, Is_true (negb a) <-> (~(Is_true a))).
Proof.
	intros.
	unfold iff.
	refine (conj _ _).
	case a.
	
		intros.
		simpl in H.
		case H.
		
		intros.
		unfold not.
		intros.
		simpl in H0.
		case H0.
		
	case a.
	
		intros.
		simpl in H.
		case H.
		exact I.
		
		intros.
		simpl.
		exact I.
Qed.

Theorem not_exists :
(forall P : Set -> Prop, ~(exists x, P x) <-> (forall x, ~ (P x))).
Proof.
    intro P.
    split.

        intros h x hpx.
        apply h.
        exact (ex_intro P x hpx).

    intros h1 h2.
    destruct h2 as [x h2].
    case (h1 x h2).
Qed.


Theorem not_forall : (forall P : Set->Prop, (exists x, ~(P x)) -> ~(forall x, P x)).
Proof.
	intros.
	unfold not.
	intros.
	case H.
	intros.
	case H1.
	exact (H0 x).
Qed.

Theorem thm_eq_sym : (forall x y : Set, x = y -> y = x).
Proof.
	intros.
	destruct H.
	exact (eq_refl x).
Qed.

Theorem thm_eq_trans : (forall x y z : Set, x = y -> y = z -> x = z).
Proof.
	intros.
	rewrite H.
	rewrite H0.
	exact (eq_refl z).
Qed.

Theorem andb_sym : (forall a b, a && b = b && a).
Proof.
	intros.
	case a, b.
	
		simpl.
		exact (eq_refl true).
		
		simpl.
		exact (eq_refl false).
		
		simpl.
		exact (eq_refl false).
		
		simpl.
		exact (eq_refl false).
Qed.

Theorem neq_nega: (forall a, a <> (negb a)).
Proof.
	intros.
	unfold not.
	case a.
	
		intros.
		simpl in H.
		discriminate H.
	
		intros.
		simpl in H.
		discriminate H.
Qed.

Theorem plus_O_n : (forall n : nat, O + n = n).
Proof.
	intros.
	simpl.
	exact (eq_refl n).
Qed.

Theorem plus_n_O : (forall n : nat, n + O = n).
Proof.
	intros.
	elim n.
	
		simpl.
		exact (eq_refl O).
		
		intros.
		simpl.
		rewrite H.
		exact (eq_refl (S n0)).
Qed.

Theorem plus_n_O_new : (forall n : nat, n + O = n).
Proof.
	intros.
	induction n as [ | n IHn].
	
		simpl.
		exact (eq_refl O).
		
		simpl.
		rewrite IHn.
		exact (eq_refl (S n)).
Qed.

Theorem plus_sym : (forall n m : nat, n + m = m + n).
Proof.
	intros.
	elim n.
	
		simpl.
		exact (eq_sym (plus_n_O m)).
		
		intros.
		simpl.
		rewrite H.
		elim m.
		
			simpl.
			exact (eq_refl (S n0)).
			
			intros.
			simpl.
			rewrite <- H0.
			exact (eq_refl (S (S (n1 + n0)))).
Qed.

Require Import List.

Theorem correctness_of_tl :
   (forall A:Type,
   (forall (x : A) (lst : list A),
   (tl (nil : list A)) = nil /\ (tl (x :: lst)) = lst)).
Proof.
	intros.
	refine (conj _ _).
	
		simpl.
		exact (eq_refl nil).
		
		simpl.
		exact (eq_refl lst).
Qed.

Definition tl_error (A : Type) (l : list A)
:=
  match l with
    | nil => None
    | _ :: l => Some l
  end.

Theorem correctness_of_tl_error :
   (forall A:Type,
   (forall (x : A) (lst : list A),
   (tl_error A nil) = None /\ (tl_error A (x :: lst)) = Some lst)).
Proof.
	intros.
	refine (conj _ _).
	
		simpl.
		exact (eq_refl None).
		
		simpl.
		exact (eq_refl (Some lst)).
Qed.

Definition tl_never_fail (A : Type) (lst : list A) (safety_proof : lst <> nil)
  : list A
:=
  (match lst as b return (lst = b -> list A) with
    | nil => (fun foo : lst = nil =>
                   match (safety_proof foo) return list A with
                   end
                )
    | _ :: t => (fun foo : lst = _ :: t =>
                   t
                )
  end) eq_refl.

Theorem correctness_of_tl_never_fail :
   (forall A:Type,
   (forall (x : A) (rest : list A),
   (exists safety_proof : ((x :: rest) <> nil),
      (tl_never_fail A (x :: rest) safety_proof) = rest))).
Proof.
	intros.
	assert (witness : (x :: rest <> nil)).
	
		unfold not.
		intros.
		discriminate H.
		
		refine (ex_intro _ witness _).
		simpl.
		exact (eq_refl rest).
Qed.

Theorem app_nil_l : (forall A:Type, (forall l:list A, nil ++ l = l)).
Proof.
	intros.
	simpl.
	exact (eq_refl l).
Qed.

Theorem app_nil_r : (forall A:Type, (forall l:list A, l ++ nil = l)).
Proof.
	intros.
	elim l.
	
		simpl.
		exact (eq_refl nil).
		
		intros.
		simpl.
		rewrite H.
		exact (eq_refl (a::l0)).
Qed.

Theorem app_comm_cons : forall A (x y:list A) (a:A), a :: (x ++ y) = (a :: x) ++ y.
Proof.
	intros.
	simpl.
	exact (eq_refl (a :: x ++ y)).
Qed.

Theorem app_assoc : forall A (l m n:list A), l ++ m ++ n = (l ++ m) ++ n.
Proof.
	intros.
	elim l.
	
		simpl.
		exact (eq_refl (m++n)).
		
		intros.
		simpl.
		rewrite <- H.
		exact (eq_refl (a :: l0 ++ m ++ n)).
Qed.

Theorem app_cons_not_nil : forall A (x y: list A) (a:A), nil <> x ++ a :: y.
Proof.
	intros.
	unfold not.
	elim x.
	
		simpl.
		elim y.
		
			intros.
			discriminate H.
			
			intros.
			discriminate H0.
			
		simpl.
		elim y.
		
			intros.
			discriminate H0.
			
			intros.
			discriminate H1.
Qed.

Theorem not_exercise : (forall A : Prop, ~~(~~A -> A)).
Proof.
	unfold not.
	intros S H1.
	apply H1.
	intro H2.
	apply False_rect.
	apply H2.
	intro H3.
	apply H1.
	intro H4.
	apply H3.
Qed.