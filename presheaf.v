Definition Subset (X : Set) : Type := X -> Prop.
Definition empty (X : Set) : Subset X := fun (x : X) => x <> x.
Inductive incl {X : Set} : Subset X -> Subset X -> Prop :=
| Incl_intro : forall U V : Subset X,
    (forall x : X, U x -> V x) -> incl U V.
Definition intsec {X : Set} (U V : Subset X) : Subset X :=
  fun (x : X) => U x /\ V x.
Definition fiber {X A : Set} (f : A -> Subset X) (V : Subset X) : Subset A :=
  fun (a : A) => V = (f a).

Hypothesis subset_equal : forall {X : Set} (U V : Subset X), (forall x : X, U x <-> V x) -> U = V.

Lemma incl_trans : forall {X : Set} (U V W : Subset X), incl U V -> incl V W -> incl U W.
  Proof.
    intros.
destruct H.
destruct H0.
apply Incl_intro.
intros.
apply H0.
apply H.
apply H1.
  Qed.

  Lemma intsec_comm : forall {X : Set} (U V : Subset X), intsec U V = intsec V U.
  Proof.
    intros.
    unfold intsec.
    apply subset_equal.
    intros.
    split.
    split.
    apply H.
    apply H.
    split.
    apply H.
    apply H.
    Qed.
Lemma inclusion : forall {X : Set} (U V : Subset X) (x : X), incl U V -> U x -> V x.
Proof.
  intros.
  destruct H.
apply H.
apply H0.
Qed.

Lemma intsec_and : forall {X : Set} (U V : Subset X) (x : X), (intsec U V) x <-> U x /\ V x.
Proof.
  intros.
  split.
  intros.
  unfold intsec in H.
  apply H.
  split.
  apply H.
  apply H.
Qed.
Lemma incl_intsec : forall {X : Set} (U V : Subset X) (x : X), incl U V -> (intsec U V) x <->  U x.
Proof.
  intros.
  unfold intsec.
  split.
  intro.
  apply H0.
  intro.
  destruct H.
  split.
  apply H0.
  apply H.
  apply H0.
Qed.
Lemma incl_intsec_eq : forall {X : Set} (U V : Subset X), incl U V -> intsec U V = U.
  Proof.
    intros.
    unfold intsec.
    apply subset_equal.
    intro.
    split.
    intro.
    apply H0.
    intro.
    split.
    apply H0.
    destruct H.
    apply H.
    apply H0.
  Qed.

Lemma fiber_in : forall {X A : Set} (U : Subset X) (a : A) (f : A -> Subset X),
        fiber f U a -> U = (f a).
Proof.
  intros.
destruct H.
reflexivity.
Qed.

(* Definition of presheaf *)

Variable X A : Set.
Variable E : A -> Subset X.
Variable r : A -> Subset X -> A.
Hypothesis A_eq : forall a b : A,  a = b -> b = a.
Hypothesis A_assoc : forall a b c : A, a = b /\ b = c -> a = c.

Hypothesis ps_empty : forall a b : A, r a (empty X) = r b (empty X).
Hypothesis r_intsec : forall a : A, forall U V : Subset X, r (r a U) V = r a (intsec U V).
Hypothesis E_domain : forall a : A, r a (E a) = a.
Hypothesis E_r : forall a : A, forall U : Subset X, E (r a U) = intsec (E a) U.

Lemma empty_idemp_lem : forall a : A, E a = empty X -> r a (empty X) = a.
  Proof.
  intros.
  apply A_eq.
  rewrite <- H.
  apply A_eq.
  apply E_domain.
Qed.  

Lemma empty_idemp : forall a b : A, ((E a) = (empty X)) -> ((E b) = (empty X)) -> a = b.
  intros.
apply empty_idemp_lem in H.
apply empty_idemp_lem in H0.
rewrite <- H.
rewrite <- H0.
apply ps_empty.
Qed.  

Lemma res_id : forall (a : A) (U : Subset X), E a = U -> r a U = a.
  intros.
  rewrite <- H.
  apply E_domain.
Qed.

Lemma res_incl : forall (a : A) (U V : Subset X), incl U V -> E a = V -> r (r a V) U = r a U.
Proof.
  intros.
  assert (r a V = a).
  rewrite <- H0.
  apply E_domain.
  f_equal.
  apply H1.
  Qed.

Lemma r_id : forall (U : Subset X) (a : A), fiber E U a -> r a U = a.
Proof.
  intros.
  assert (U = (E a)).
  apply fiber_in.
  apply H.
  rewrite H0.
    apply E_domain.
Qed.

Lemma subset_eq_comm : forall U V :Subset X, U = V -> V = U.
Proof.
  intros.
  apply subset_equal.
  intros.
  destruct H.
  split.
  auto.
  auto.
  Qed.

Lemma r_trans : forall (U V W : Subset X) (a : A), incl U V -> incl V W -> E a = W -> r (r a V) U = r a U.
Proof.  
  intros.
  assert (r (r a V) U = r a (intsec V U)).
  apply r_intsec.
  assert (intsec U V = U).
  apply incl_intsec_eq.
  apply H.
  rewrite H2.
  f_equal.
  apply subset_eq_comm.
  apply subset_eq_comm in H3.
  assert (intsec U V = intsec V U).
  apply intsec_comm.
  rewrite <- H4.
  apply H3.
Qed.


  
  

                                                                             
                                                                    