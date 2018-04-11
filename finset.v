Require Import Ensembles.
Require Import Classical.

Variable U : Type.
Inductive Finite : Ensemble U -> Prop :=
| Empty_is_finite : Finite (Empty_set U)
| Union_is_finite : forall A : Ensemble U, Finite A -> forall x : U, ~ In U A x -> Finite (Add U A x).
Inductive cardinal : Ensemble U -> nat -> Prop :=
| card_empty : cardinal (Empty_set U) 0
| card_add : forall (A : Ensemble U) (n : nat), cardinal A n -> forall x : U, ~ In U A x -> cardinal (Add U A x) (S n).
Lemma cardinal_zero : forall X : Ensemble U, cardinal X O -> forall x : U, ~ In U X x.
Proof.
  intros.
  inversion H.
  intro.
  unfold In in H1.
  inversion H1.
Qed.
Lemma singleton_add : forall x : U, Singleton U x = Add U (Empty_set U) x.
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set.
  split.
  unfold Included.
  intros.
  inversion H.
  unfold In.
  unfold Add.
  subst.
  apply Union_intror.
  apply H.
  unfold Included.
  intros.
  unfold In.
  unfold In in H.
  unfold Add in H.
  destruct H.
  destruct H.
  destruct H.
  reflexivity.
Qed.  
Lemma singleton_one : forall x : U, cardinal (Singleton U x) (S O).
Proof.
  intros.
  assert (Singleton U x = Add U (Empty_set U) x).
  apply singleton_add.
  rewrite H.
  apply card_add.
  apply card_empty.
  intro.
  inversion H0. 
Qed.
Lemma cardinal_invert :
  forall (X : Ensemble U) (p : nat),
    cardinal X p ->
    match p with
    | O => X = Empty_set U
    | S n => exists A : _, (exists x : _, X = Add U A x /\ ~ In U A x /\ cardinal A n)
    end.
Proof.
  intros.
  inversion H.
  reflexivity.
  exists A.
  exists x.
  intuition.
Qed.
Lemma cardinal_elim :
  forall (X : Ensemble U) (p : nat),
    cardinal X p ->
    match p with
    | O => X = Empty_set U
    | S n => Inhabited U X
    end.
Proof.
  intros.
  inversion H.
  reflexivity.
  apply (Inhabited_intro U (Add U A x) x).
  unfold In.
  unfold Add.
  apply Union_intror.
  unfold In.
  intuition.
Qed.  
Lemma positive_cardinal : forall (X : Ensemble U) (n : nat), cardinal X (S n) -> exists x : U, In U X x.
Proof.
  intros.
  apply (cardinal_elim X (S n)) in H.
  destruct H.
  exists x.
  apply H.
Qed.
Lemma union_add : forall (X Y : Ensemble U) (x : U), Union U (Add U X x) Y = Add U (Union U X Y) x.
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set.
  split.
  unfold Included.
  intros.
  unfold In.
  unfold Add.
  unfold In in H.
  destruct H.
  unfold In in H.
  unfold Add in H.
  destruct H.
  apply Union_introl.
  unfold In.
  apply Union_introl.
  apply H.
  apply Union_intror.
  apply H.
  apply Union_introl.
  unfold In.
  apply Union_intror.
  apply H.
  unfold Included.
  intros.
  unfold In in H.
  unfold Add in H.
  unfold In.
  destruct H.
  unfold In in H.
  destruct H.
  apply Union_introl.
  unfold In.
  unfold Add.
  apply Union_introl.
  apply H.
  apply Union_intror.
  apply H.
  apply Union_introl.
  unfold In.
  unfold Add.
  apply Union_intror.
  apply H.
Qed.
Lemma union_empty : forall X : Ensemble U, Union U (Empty_set U) X = X.
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set.
  split.
  subst.
  unfold Included.
  intros.
  unfold In in H.
  case H.
  intros.
  inversion H0.
  intros.
  apply H0.
  unfold Included.
  intros.
  unfold In.
  apply Union_intror.
  apply H.
Qed.  
Lemma finite_disjoint_union : forall (n : nat) (X Y : Ensemble U), cardinal X n -> Finite Y -> Disjoint U X Y -> Finite (Union U X Y).
Proof.
  intro n.
  induction n.
  intros.
  inversion H.
  assert (Union U (Empty_set U) Y = Y).
  apply union_empty.
  rewrite H3.
  apply H0.
  intros.
  inversion H.
  assert (~ In U Y x).
  destruct H1.
  specialize H1 with x.
  intro.
  assert (In U X x).
  unfold Add in H4.
  destruct H4.
  unfold In.
  apply Union_intror.
  unfold In.
  reflexivity.
  assert (In U (Intersection U X Y) x).
  unfold In.
  apply Intersection_intro.
  apply H7.
  apply H6.
  intuition.
  assert (Union U (Add U A x) Y = Add U (Union U A Y) x).
  apply union_add.
  rewrite H7.
  apply Union_is_finite.
  apply IHn.
  apply H3.
  apply H0.
  apply Disjoint_intro.
  intros.
  intro.
  unfold In in H8.
  destruct H8.
  destruct H1.
  specialize H1 with x0.
  unfold In in H1.
  assert (In U X x0).
  rewrite <- H4.
  unfold In.
  unfold Add.
  apply Union_introl.
  apply H8.
  assert (In U (Intersection U X Y) x0).
  unfold In.
  apply Intersection_intro.
  apply H10.
  apply H9.
  intuition.
  intro.
  unfold In in H8.
  destruct H8.
  intuition.
  intuition.
Qed.
Lemma finite_cardinal : forall X : Ensemble U, Finite X -> exists n : nat, cardinal X n.
Proof.
  intros.
  induction H.
  exists 0.
  apply card_empty.
  destruct IHFinite.
  exists (S x0).
  apply card_add.
  apply H1.
  apply H0.
Qed.

Lemma sub_disj : forall X Y : Ensemble U, Included U X Y -> Y = Union U X (Setminus U Y X) /\ Disjoint U X (Setminus U Y X).
Proof.
  intros.
  assert (forall x : U, In U X x \/ ~ In U X x).
  intros.
  apply classic.
  split.
  assert (forall x : U, In U Y x -> In U X x \/ In U (Setminus U Y X) x).
  intros.
  specialize H0 with x.
  case H0.
  intuition.
  intros.
  right.
  unfold In.
  unfold Setminus.
  intuition.
  apply Extensionality_Ensembles.
  unfold Same_set.
  split.
  unfold Included.
  intros.
  specialize H1 with x.
  apply H1 in H2.
  case H2.
  intros.
  unfold In.
  apply Union_introl.
  apply H3.
  intros.
  apply Union_intror.
  apply H3.
  unfold Included.
  intros.
  unfold In in H2.
  destruct H2.
  unfold Included in H.
  apply H in H2.
  apply H2.
  unfold In in H2.
  unfold Setminus in H2.
  apply H2.
  apply Disjoint_intro.
  intros.
  intro.
  unfold In in H1.
  destruct H1.
  unfold In in H1.
  unfold In in H2.
  unfold Setminus in H2.
  intuition.
Qed.
(*
Lemma finite_subset : forall X Y : Ensemble U, Included U X Y -> Finite Y -> Finite X.
Proof.
  intros.
  induction H0.
  assert (X = Empty_set U).
  apply Extensionality_Ensembles.
  unfold Same_set.
  split.
  apply H.
  unfold Included.
  intros.
  destruct H0.
  rewrite H0.
  apply Empty_is_finite.
  apply IHFinite
  unfold Included in H.
  unfold Included.
  intros.
  specialize H with x0.
  destruct H.
  apply H2.
  apply H.
  unfold In in H.
  destruct H.
  apply H1.
*)
(*  
Lemma union_decompose : forall X Y : Ensemble U, Union U X Y = Union U (Union U (Setminus U X Y) (Intersection U X Y)) (Setminus U Y X).
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set.
  split.
  unfold Included.
  intros.
  unfold In.
  unfold In in H.
  case H.
  intros.
  unfold In in H0.
  assert (X = Union U (Intersection U X Y) (Setminus U X Y)).
  apply Extensionality_Ensembles.
  unfold Same_set.
  split.
  unfold Included.
  intros.
  unfold In.
  apply Union_introl
  apply H1.
  unfold Included.
  intros.
  unfold In in H1.
  case H1.
  intuition.
  intuition.
  unfold In in H2.
  unfold Setminus in H2.
  apply H2.
  assert (In U (Union U (Intersection U X Y) (Setminus U X Y)) x0).
  rewrite <- H1.
  apply H0.
  unfold In in H2.
  destruct H2.
  apply Union_introl.
  unfold In.
  apply Union_introl
  apply H2.
  
  subst.
  rewrite <- H0 in H1.
  intuition.

  apply 
  case H0.
*)
  
(*
Lemma fin_union : forall X Y : Ensemble U, Finite X -> Finite Y -> Finite (Union U X Y).
Proof.
  intros.
*)  
  

  