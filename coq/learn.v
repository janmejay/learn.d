Check nat.


Check 10 = 20.

Compute 2 + 2.

Compute 3 + 4.

Compute 1 + 2.

Definition sum5 := fun a b c d e : nat => a + b + c + d + e.

Check sum5.

Compute sum5 1 2 3 4 5.

Require Import Bool.
Require Import Arith.
Require Import List.

Fixpoint insert n l := 
    match l with 
    |  nil => n::nil
    | h::t => if n <=? h then n::l else h::insert n t
    end.

Fixpoint sort l :=
    match l with 
    |  nil => nil
    | h::t => insert h (sort t)
    end.

Compute sort (10::5::3::13::7::1::0::nil).

Definition head_lte l :=
    match l with
      nil => true
    | h::nil => true
    | h::n::t => h <=? n
    end.

Fixpoint is_sorted l := 
    match l with 
      h::t => if head_lte l then is_sorted t else false
    | nil => true
    end.

Fixpoint count n l := 
    match l with
      nil => 0
    | h::t => if n =? h then 1 + count n t else count n t
    end.

Search True.

Lemma prop_conj : forall a b : Prop, a /\ b -> b /\ a.
Proof.
    intros a b H.
    split.
    destruct H as [H1 H2].
    exact H2.
    intuition.
Qed.

Lemma prop_disj : forall a b : Prop, a \/ b -> b \/ a.
Proof.
    intros a b H.
    destruct H as [H1 | H2].
    right; assumption.
    left; assumption.
Qed.

Lemma prop_3_5: 3 <= 5.
Proof.
    SearchPattern (_ <= S _).
    apply le_S.
    apply le_S.
    apply le_n.
Qed.


Check le_trans.

Lemma x10y : forall x y : nat, x <= 10 -> 10 <= y -> x <= y.
Proof.
    intros x y x10 y10.
    apply le_trans with (m := 10).
    assumption.
    assumption.
Qed.


Lemma add_sq: forall x y : nat, (x + y) * (x + y) = x * x + 2 * x * y + y * y.
Proof.
    intros x y.
    rewrite Nat.mul_add_distr_l.
    rewrite Nat.mul_add_distr_r.
    rewrite Nat.mul_add_distr_r.
    rewrite Nat.add_assoc.
    rewrite <- Nat.mul_1_l with (n := y * x).
    rewrite Nat.mul_comm with (n := y) (m := x).
    rewrite <- Nat.add_assoc with (n := x * x).
    rewrite <- Nat.mul_succ_l with (n := 1) (m := x * y).
    rewrite Nat.mul_assoc.
    reflexivity.
Qed.

Print Nat.pred.

Lemma pred_S_eq: forall x y : nat, x = S y -> pred x = y.
Proof.
    intros x y q.
    unfold pred.
    rewrite q.
    reflexivity.
Qed.

Require Import Omega.

Lemma omega_eg: forall f x y, 0 < x -> 0 < f x -> 3 * f x < 2 * y -> f x < y.
Proof.
    intros.
    omega.
Qed.

Lemma e3_1: forall A B C: Prop, A /\ (B /\ C) -> (A /\ B) /\ C.
Proof.
    intros.
    firstorder.
Qed.

Lemma e3_1_man: forall A B C: Prop, A /\ (B /\ C) -> (A /\ B) /\ C.
Proof.
    intros.
    destruct H.
    destruct H0.
    split.
    split.
    apply H.
    apply H0.
    apply H1.
Qed.

Lemma e3_2: forall A B C D : Prop, (A -> B) /\ (C -> D) /\ A /\ C -> B /\ D.
Proof.
    firstorder.
Qed.

Lemma e3_2_man: forall A B C D : Prop, (A -> B) /\ (C -> D) /\ A /\ C -> B /\ D.
Proof.
    intros.
    destruct H.
    destruct H0.
    destruct H1.
    split.
    apply H; apply H1.
    apply H0; apply H2.
Qed.

Lemma e3_3: forall A : Prop, ~(A /\ ~A).
Proof.
    tauto.
Qed.

Print e3_3.

Lemma e3_3_man: forall A : Prop, ~(A /\ ~A).
Proof.
    intros.
    unfold not.
    intros.
    destruct H.
    contradiction.
Qed.

Lemma e3_4: forall A B C : Prop, A \/ (B \/ C) -> (A \/ B) \/ C.
Proof.
    firstorder.
Qed.

Lemma e3_4_man: forall A B C : Prop, A \/ (B \/ C) -> (A \/ B) \/ C.
Proof.
    intros.
    compute.
    apply or_assoc.
    apply H.
Qed.

Lemma e3_5: forall A B : Prop, (A \/ B) /\ ~A -> B.
Proof.
    tauto.
Qed.

Lemma e3_5_man: forall A B : Prop, (A \/ B) /\ ~A -> B.
Proof.
    intros.
    destruct H.
    destruct H.
    contradiction.
    apply H.
Qed.

Lemma e3_uc_1: forall A: Type,
    forall P Q : A -> Prop,
        (forall x, P x) \/ (forall y, Q y) -> forall x, P x \/ Q x.
Proof.
    firstorder.
Qed.

Lemma e3_uc_1_man: forall A: Type,
    forall P Q : A -> Prop,
        (forall x, P x) \/ (forall y, Q y) -> forall x, P x \/ Q x.
Proof.
    intros.
    destruct H.
    specialize (H x).
    apply or_introl.
    exact H.
    specialize (H x).
    apply or_intror.
    exact H.
Qed.

Print e3_uc_1.
    
Print e3_uc_1_man.

Search "sum_n".

Require Import ArithRing Ring.


Fixpoint sum_n n := 
    match n with 
    | 0 => 0
    | S p => p + sum_n p
    end.

Compute sum_n 3.

Lemma sum_of_first_n_nat_short: forall n, 2 * sum_n n + n = n * n.
Proof.
    induction n.
    reflexivity.
    assert (SnSn : S n * S n = n * n + 2 * n + 1).
    ring.
    rewrite SnSn.
    rewrite <- IHn.
    simpl.
    ring.
Qed.

Lemma S_add_1: forall n, S n = n + 1.
Proof.
    intros.
    induction n.
    reflexivity.
    ring.
Qed.


Lemma Sn_n_plus_1: forall n m, m + S n = S (n + m).
Proof.
    intros.
    induction m.
    ring.
    ring.
Qed.

Lemma sum_of_first_n_nat_man: forall n, 2 * sum_n n + n = n * n.
Proof.
    induction n.
    simpl.
    reflexivity.
    simpl sum_n.
    rewrite Nat.mul_add_distr_l.
    assert (double_n: 2 * n = n + n).
    induction n.
    ring.
    ring.
    rewrite double_n.
    rewrite Nat.add_comm with (m := 2 * sum_n n).
    rewrite Nat.add_assoc.
    rewrite IHn.
    rewrite S_add_1.
    ring.
Qed.

Fixpoint evenb n := 
    match n with 
    | 0 => true
    | 1 => false
    | S (S p) => evenb p
    end.

Lemma evenb_p_given : forall n, evenb n = true -> exists x, n = 2 * x.
Proof.
    assert (Main: forall n, (evenb n = true -> exists x, n = 2 * x) /\
                            (evenb (S n) = true -> exists x, S n = 2 * x)).
    induction n.
    split. 
        exists 0.  reflexivity.
        simpl. intros H. discriminate H.
    split.
        destruct IHn as [_ IHn_r]. exact IHn_r.
        simpl evenb. intros H. destruct IHn as [IHn_l _]. 
        assert (H' : exists x, n = 2 * x).
        apply IHn_l. apply H.
        destruct H' as [x q]. exists (x + 1). rewrite q. ring.
        intros.
        destruct (Main n) as [mL _]. apply mL. exact H.
Qed.

Lemma evenb_p_man : forall n, evenb n = true -> exists x, n = 2 * x.
Proof.
    assert (C: forall k, (evenb k = true -> exists x, k = 2 * x) /\
                         (evenb (S k) = true -> exists x, S k = 2 * x)).
        induction k.
        split. exists 0. reflexivity.
        simpl evenb. intro H. discriminate H.
        split. destruct IHk as [_ IHk_r]. exact IHk_r.
        simpl evenb. intros H. destruct IHk as [IHk_l _].
        assert (H': exists x,  k = 2 * x). apply IHk_l. exact H.
        destruct H' as [x q]. exists (x + 1). rewrite q. ring.
    induction n.
    exists 0. reflexivity.
    destruct (C n) as [_ C_r]. exact C_r.
Qed.

(*  Ch4 exercise 1 *)

Fixpoint add n m := 
    match n with
        | 0 => m
        | S p => add p (S m)
    end.

Lemma ch4_add_0: forall k, add 0 k = k.
Proof.
    simpl. reflexivity.
Qed.

Theorem ch4_tp_1: forall n m, add n (S m) = S (add n m).
Proof.
    induction n.
    intro m.
    apply ch4_add_0.
    simpl.
    intro m.
    rewrite IHn.
    reflexivity.
Qed.

Theorem ch4_tp_2: forall n m, add (S n) m = S (add n m).
Proof.
    assert (forall n m, add (S n) m = add n (S m)).
        induction n.
        simpl. reflexivity.
        simpl. intro. rewrite <- IHn. reflexivity.
    intros.
    rewrite H.
    apply ch4_tp_1.
Qed.

Theorem ch4_tp_3: forall n m, add n m = n + m.
Proof.
    induction n. apply ch4_add_0.
    intro.
    rewrite ch4_tp_2.
    rewrite IHn.
    reflexivity.
Qed.

(** Ch4 ex 2 **)

Fixpoint sum_odd_n (n: nat): nat :=
    match n with
        | 0 => 0
        | S p => 1 + 2 * p + sum_odd_n p
    end.

Theorem ch4_sum_of_odd_n_sq: forall n: nat, sum_odd_n n = n * n.
Proof.
    induction n.
    simpl. reflexivity.
    simpl.
    rewrite IHn.
    ring.
Qed.

(** Ch 5 **)

Definition is_zero (x: nat): bool := 
    match x with 
        | 0 => true
        | S _ => false
    end.

Lemma not_is_zero_pred: forall x,
    is_zero x = false -> S (Nat.pred x) = x.
Proof.
    intros x.
    unfold is_zero, Nat.pred.
    destruct x as [ | p].
    discriminate.
    intros h. reflexivity.
Qed.

(** Ch 6 **)

Lemma insert_incr: forall n l, count n (insert n l) = 1 + count n l.
Proof.
    intros n l.
    induction l.
        simpl.
        rewrite Nat.eqb_refl. reflexivity.
    simpl. 
        case (n <=? a).
        simpl.
        rewrite Nat.eqb_refl.
        reflexivity.
    simpl.
        case (n =? a).
        rewrite IHl.
        reflexivity.
    rewrite IHl.
    reflexivity.
Qed.

(** Ch 7 **)

Inductive bin: Type := 
  | L: bin
  | N: bin -> bin -> bin.

Check N L (N L L).

(** Ch 7 Ex 1 **)

Inductive Et: Type :=
  | EtC: Et
  | Et3: nat -> Et -> Et -> Et
  | Et4: bool -> Et -> Et -> Et -> Et.

Definition Not_NLL(t: bin): bool := 
    match t with 
      | N L L => false
      | _ => true
    end.

Compute Not_NLL (N L L).
Compute Not_NLL (N L (N L L)).
Compute Not_NLL L.

Fixpoint flatten_aux(t1 t2: bin): bin :=
    match t1 with
      | L => N L t2
      | N t'1 t'2 => flatten_aux t'1 (flatten_aux t'2 t2)
    end.

Compute flatten_aux (N (N L L) (N L L)) L.

Fixpoint flatten(t: bin): bin := 
    match t with 
      | L => L
      | N t1 t2 => flatten_aux t1 (flatten t2)
    end.

Compute flatten (N (N L (N L L)) (N (N L L) L)).

Fixpoint size(t: bin): nat := 
    match t with
      | L => 1
      | N t1 t2 => 1 + size(t1) + size(t2)
    end.

Compute size (N L L).
Compute size (N (N L (N L L)) (N (N L L) L)).

Fixpoint l_count(t: bin): nat := 
    match t with
      | L => 1
      | N t1 t2 => l_count(t1) + l_count(t2)
    end.

Compute l_count(N L L).
Compute l_count(N (N L (N L L)) (N (N L L) L)).

Lemma Not_NLL_size: forall t, Not_NLL t = false -> size t = 3.
Proof.
    intros t.
    destruct t.
    simpl. 
    discriminate.
    destruct t1.
    destruct t2.
    simpl.
    intro.
    reflexivity.
    simpl.
    discriminate.
    simpl.
    discriminate.
Qed.

Lemma flatten_aux_size: forall t1 t2: bin, size(flatten_aux t1 t2) = 1 + size(t1) + size(t2).
Proof.
    induction t1.
    intro t2.
    simpl.
    reflexivity.
    intros t2.
    simpl.
    rewrite IHt1_1.
    rewrite IHt1_2.
    ring.
Qed.

(** Ch7.5 ex **)

Lemma flatten_size: forall t, size (flatten t) = size t.
Proof.
    induction t.
    reflexivity.
    simpl flatten.
    simpl size at 1.
    rewrite flatten_aux_size.
    rewrite IHt2.
    reflexivity.
Qed.

(** Ch 7.6 **)

Lemma not_subterm_self_l: forall x y, ~ x = N x y.
Proof.
    induction x.
    intros y r.
    discriminate.
    intros y r.
    injection r.
    intros.
    assert(IHx1': x1 <>  N x1 x2).
    apply IHx1.
    contradiction.
Qed.

(** Ch 8 **)

Fixpoint fact(n: nat): nat := 
    match n with 
        | 0 => 1
        | S p => n * fact(p)
    end.

Compute fact(5).

Fixpoint fib(n: nat): nat := 
    match n with
        | 0 => 0
        | S q =>
            match q with 
                | 0 => 1
                | S p => fib p + fib q
            end
    end.

