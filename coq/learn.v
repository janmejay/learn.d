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
    | h::t => if h =? n then 1 + count n t else count n t
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
    


