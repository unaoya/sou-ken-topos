(*
http://ccvanishing.hateblo.jp/entry/2013/01/06/212707
https://gist.github.com/y-taka-23/4466805A
*)
Definition Subset (X : Set) : Type := X -> Prop.
Axiom subset_equal : forall {X : Set} (U V : Subset X), U = V <-> forall x : X, U x <-> V x.
Definition whole (X : Set) : Subset X := fun (x : X) => x = x.
Definition empty (X : Set) : Subset X := fun (x : X) => x <> x.
Inductive incl {X : Set} : Subset X -> Subset X -> Prop :=
| Incl_intro : forall S1 S2 : Subset X,
    (forall x : X, S1 x -> S2 x) ->
    incl S1 S2.
Lemma whole_incl_all {X : Set} : forall U : Subset X, incl U (whole X).
Proof.
  intros.
  apply Incl_intro.
  intros.
  unfold whole.
  auto.
Qed.
Lemma all_incl_empty {X : Set} : forall U : Subset X, incl (empty X) U.
Proof.
  intros.
  apply Incl_intro.
  intros.
  unfold empty in H.
  destruct H.
  auto.
Qed.
Lemma incl_id {X : Set} : forall U : Subset X, incl U U.
Proof.
  intros.
  apply Incl_intro.
  intros.
  apply H.
Qed.  
Lemma incl_trans {X : Set} : forall U V W : Subset X, incl U V -> incl V W -> incl U W.
Proof.
  intros.
  destruct H.
  destruct H0.
  apply Incl_intro.
  intros.
  auto.
Qed.
Lemma incl_in {X : Set} : forall (U V : Subset X) (x : X), incl U V -> U x -> V x.
Proof.
  intros.
  destruct H.
  apply H.
  apply H0.
Qed.  
Lemma incl_equal {X : Set} : forall U V : Subset X, incl U V -> incl V U -> U = V.
Proof.
  intros.
  apply subset_equal.
  intros.
  split.
  intro.
  destruct H.
  apply H.
  apply H1.
  intro.
  destruct H0.
  apply H0.
  apply H1.
Qed.

Definition bigcap {X : Set} (I : Set) (index : I -> Subset X) : Subset X :=
  fun (x : X) => forall i : I, (index i) x.
Definition intsec {X : Set} (S1 S2 : Subset X) :=
  let index (b : bool) := match b with
                          | true => S1
                          | false  => S2
                          end in
  bigcap bool index.
Lemma intsec_in {X : Set} : forall (U V : Subset X) (x : X), (intsec U V) x -> U x.
Proof.
  intros.  
  unfold intsec in H.  
  unfold bigcap in H.
  specialize H with true.
  simpl in H.
  apply H.
Qed.  
Lemma intsec_incl {X : Set} : forall U V : Subset X, incl (intsec U V) U.
Proof.  
  intros.
  split.
  apply intsec_in.
Qed.
Lemma intsec_and : forall {X : Set} (S1 S2 : Subset X) (x : X),
    (intsec S1 S2) x <-> S1 x /\ S2 x.
Proof.
  intros.
  split.
  intro.
  split.
  apply (intsec_in S1 S2 x).
  apply H.
  unfold intsec in H.
  unfold bigcap in H.
  specialize H with false.
  simpl in H.
  apply H.
  intro.
  unfold intsec.
  unfold bigcap.
  induction i.
  apply H.
  apply H.
Qed.
Lemma intsec_comm : forall {X : Set} (U V : Subset X), intsec U V = intsec V U.
Proof.
  intros.
  apply subset_equal.
  intro.
  split.
  intro.
  apply intsec_and.
  apply intsec_and in H.
  intuition.
  intro.
  apply intsec_and.
  apply intsec_and in H.
  intuition.
Qed.
Lemma incl_intsec : forall {X : Set} (U V W : Subset X), incl W U -> incl W V -> incl W (intsec U V).
Proof.
  intros.
  apply Incl_intro.
  intros.
  apply intsec_and.
  split.
  apply (incl_in W U x).
  apply H.
  apply H1.
  apply (incl_in W V x).
  apply H0.
  apply H1.
Qed.
Lemma intsec_equle {X : Set} : forall U V : Subset X, incl U V -> intsec U V = U.
Proof.
  intros.
  apply incl_equal.
  apply intsec_incl.
  apply incl_intsec.
  apply incl_id.
  apply H.
Qed. 

Definition bigcup {X : Set} (I : Set) (index : I -> Subset X) : Subset X :=
  fun (x : X) => exists i : I, (index i) x.
Definition union {X : Set} (S1 S2 : Subset X) : Subset X :=
  let index (b : bool) := match b with
                          | true => S1
                          | false => S2
                          end in
  bigcup bool index.
Lemma union_in {X : Set} : forall (U V : Subset X) (x : X), U x -> (union U V) x.
Proof.
  intros.  
  unfold union.  
  unfold bigcup.
  exists true.
  auto.
Qed.
Lemma union_incl {X : Set} : forall U V : Subset X, incl U (union U V).
Proof.  
  intros.
  apply Incl_intro.
  apply union_in.
Qed.
Lemma union_or : forall {X : Set} (S1 S2 : Subset X) (x : X),
    (union S1 S2) x <-> S1 x \/ S2 x.
Proof.
  intros.
  split.
  intro.
  unfold union in H.
  unfold bigcup in H.
  destruct H as [i H_i].
  induction i.
  left.
  apply H_i.
  right.
  apply H_i.
  intro.
  unfold union.
  unfold bigcup.
  destruct H as [H | H].
  exists true.
  apply H.
  exists false.
  apply H.
Qed.
Lemma union_comm {X : Set} : forall U V : Subset X, union U V = union V U.
Proof.
  intros.
  apply subset_equal.
  intro.
  split.
  intro.
  apply union_or.
  apply union_or in H.
  intuition.
  intro.
  apply union_or.
  apply union_or in H.
  intuition.
Qed.
Lemma incl_union {X : Set} : forall U V W : Subset X, incl U W -> incl V W -> incl (union U V) W.
Proof.
  intros.
  apply Incl_intro.
  intros.
  apply union_or in H1.
  case H1.
  apply incl_in.
  apply H.
  apply incl_in.
  apply H0.
Qed.  
Lemma union_equle {X : Set} : forall U V : Subset X, incl U V -> V = union U V.
Proof.
  intros.
  apply incl_equal.
  assert (union U V = union V U).
  apply (union_comm U V).
  rewrite H0.
  apply union_incl.
  apply incl_union.
  apply H.
  apply incl_id.
Qed.


Definition composite {X Y Z : Set} (g : Y -> Z) (f : X -> Y) : X -> Z :=
  fun (x : X) => g (f x).
Definition image {X Y : Set} (f : X -> Y) (U : Subset X) : Subset Y :=
  fun (y : Y) => exists x : X, U x /\ f x = y.
Definition preimage {X Y : Set} (f : X -> Y) (V : Subset Y) : Subset X :=
  fun (x : X) => V (f x).
Lemma im_incl {X Y : Set} : forall (f : X -> Y) (U V : Subset X), incl U V -> incl (image f U) (image f V).
Proof.
  intros.
  apply Incl_intro.
  intros.
  unfold image.
  unfold image in H0.
  inversion H0.
  destruct H0.
  exists x0.
  split.
  apply (incl_in U V x0).
  apply H.
  apply H1.
  apply H1.
Qed.  
Lemma im_intsec {X Y : Set} : forall (f : X -> Y) (U V : Subset X), incl (image f (intsec U V)) (intsec (image f U) (image f V)).
Proof.
  intros.
  apply incl_intsec.
  apply im_incl.
  apply intsec_incl.
  apply im_incl.
  assert (intsec U V = intsec V U).
  apply intsec_comm.
  rewrite H.
  apply intsec_incl.
Qed.  
Lemma im_union {X Y : Set} : forall (f : X -> Y) (U V : Subset X), union (image f U) (image f V) = image f (union U V).
Proof.
  intros.
  apply incl_equal.
  apply incl_union.
  apply im_incl.
  apply union_incl.
  apply im_incl.
  assert (union U V = union V U).
  apply union_comm.
  rewrite H.
  apply union_incl.
  assert (incl (image f U) (union (image f U) (image f V))).
  apply union_incl.
  assert (incl (image f V) (union (image f U) (image f V))).
  assert (union (image f U) (image f V) = union (image f V) (image f U)).
  apply union_comm.
  rewrite H0.
  apply union_incl.
  apply Incl_intro.
  intros.
  unfold image in H1.
  destruct H1.
  destruct H1.
  case H1.
  intros.
  induction x1.
  apply (incl_in (image f U) (union (image f U) (image f V)) x).
  apply H.
  unfold image.
  exists x0.
  intuition.
  apply (incl_in (image f V) (union (image f U) (image f V)) x).
  apply H0.
  unfold image.
  exists x0.
  intuition.
Qed.
Lemma preim_incl {X Y : Set} : forall (f:X -> Y) (U V :Subset Y), incl U V -> incl (preimage f U) (preimage f V).
Proof.
  intros.
  apply Incl_intro.
  intros.
  unfold preimage.
  apply (incl_in U V (f x)).
  apply H.
  unfold preimage in H0.
  apply H0.
Qed.  
Lemma preim_intsec {X Y : Set} : forall (f:X -> Y) (U V : Subset Y), preimage f (intsec U V) = intsec (preimage f U) (preimage f V).
Proof.
  intros.
  apply incl_equal.
  apply incl_intsec.
  apply preim_incl.
  apply intsec_incl.
  apply preim_incl.
  assert (intsec U V = intsec V U).
  apply intsec_comm.
  rewrite H.
  apply intsec_incl.
  apply Incl_intro.
  intros.
  apply intsec_and in H.
  unfold preimage.
  unfold preimage in H.
  apply intsec_and.
  apply H.
Qed.  
Lemma preim_union {X Y:Set} : forall (f:X -> Y) (U V:Subset Y), preimage f (union U V) = union (preimage f U) (preimage f V).
Proof.
  intros.
  apply incl_equal.
  apply Incl_intro.
  intros.
  apply union_or.
  unfold preimage.
  unfold preimage in H.
  apply union_or in H.
  intuition.
  apply incl_union.
  apply preim_incl.
  apply union_incl.
  apply preim_incl.
  assert (union U V = union V U).
  apply union_comm.
  rewrite H.
  apply union_incl.
Qed.
Lemma im_preim {X Y : Set} : forall (f:X -> Y) (U:Subset X), incl U (preimage f (image f U)).
Proof.
  intros.
  apply Incl_intro.
  intros.
  unfold preimage.
  unfold image.
  exists x.
  intuition.
Qed.  
Lemma preim_im {X Y:Set} : forall (f:X -> Y) (U:Subset Y), incl (image f (preimage f U)) U.
Proof.
  intros.
  apply Incl_intro.
  intros.
  unfold image in H.
  destruct H.
  unfold preimage in H.
  intuition.
  subst.
  intuition.
Qed.  
Lemma compos_preim {X Y Z : Set} : forall (f:X -> Y) (g:Y -> Z) (U : Subset Z), preimage f (preimage g U) = preimage (composite g f) U.
Proof.
  intros.
  apply subset_equal.
  split.
  intros.
  unfold preimage.
  unfold preimage in H.
  unfold composite.
  auto.
  intros.
  unfold preimage in H.
  unfold preimage.
  unfold composite in H.
  auto.
Qed.  
Lemma compos_im {X Y Z : Set} : forall (f:X -> Y) (g:Y -> Z) (U : Subset X), image g (image f U) = image (composite g f) U.
Proof.
  intros.
  apply subset_equal.
  split.
  intros.
  unfold image.
  unfold image in H.
  destruct H.
  destruct H.
  destruct H.
  destruct H.
  unfold composite.
  exists x1.
  subst.
  intuition.
  intros.
  unfold image.
  unfold image in H.
  destruct H.
  destruct H.
  unfold composite in H0.
  exists (f x0).
  split.
  exists x0.
  intuition.
  apply H0.
Qed.
Lemma image_push : forall {X Y : Set} (S: Subset X) (f:X -> Y) (x : X),
    S x -> (image f S) (f x).
Proof.
  intros.
  unfold image.
  exists x.
  split.
  apply H.
  reflexivity.
Qed.
Lemma preimage_pull : forall {X Y : Set} (S : Subset Y) (f:X -> Y) (x : X),
    S (f x) -> preimage f S x.
Proof.
  intros.
  unfold preimage.
  apply H.
Qed.
