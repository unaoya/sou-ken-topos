(*
http://ccvanishing.hateblo.jp/entry/2013/01/06/212707
https://gist.github.com/y-taka-23/4466805A
 *)
Require Import subset.

Class TopSpace (X : Set) (Open : Subset X -> Prop) :=
  {
    TS_whole : Open (whole X);
    TS_empty : Open (empty X);
    TS_intsec : forall U1 U2 : Subset X,
        Open U1 -> Open U2 -> Open (intsec U1 U2);
    TS_union : forall (I : Set) (index : I -> Subset X),
        (forall i : I, Open (index i)) -> Open (bigcup I index)
  }.
Class Continuous (X : Set) (XOpen : Subset X -> Prop)
      (Y : Set) (YOpen : Subset Y -> Prop)
      (f : X -> Y) :=
  {
    Conti_TopSpace_l :>
                     TopSpace X XOpen;
    Conti_TopSpace_r :>
                     TopSpace Y YOpen;
    Conti_preim :
      forall V : Subset Y, YOpen V -> XOpen (preimage f V)
  }.
Class Connected (X : Set) (Open : Subset X -> Prop) (S : Subset X) :=
  {
    Conn_TopSpace :> TopSpace X Open;
    Conn_insep :
      forall U1 U2 : Subset X,
        Open U1 -> Open U2 -> incl S (union U1 U2) ->
        (exists x1 : X, (intsec S U1) x1) ->
        (exists x2 : X, (intsec S U2) x2) ->
        exists x : X, intsec S (intsec U1 U2) x
  }.
Definition identity (X : Set) : X -> X := fun (x : X) => x.
                                                   
Class Homeomorphism (X Y : Set) (XOpen : Subset X -> Prop) (YOpen : Subset Y -> Prop) (f : X -> Y) :=
  {
    Homeo_conti :> Continuous X XOpen Y YOpen f;
    Homeo_bijec :
      exists g : Y -> X,
        composite g f = identity X ->
        composite f g = identity Y ->
        Continuous Y YOpen X XOpen g
  }.
Class Locally_homeo (X Y : Set) (XOpen : Subset X -> Prop) (YOpen : Subset Y -> Prop) (f : X -> Y) :=
  {
    LH_conti :> Continuous X XOpen Y YOpen f;
    LH_locinv :
      forall x : X, exists U : Subset X, U x -> XOpen U -> Homeomophism U (image (restr f U)) 

Section Connectedness.

Variables X Y : Set.
Variable XOpen : Subset X -> Prop.
Variable YOpen : Subset Y -> Prop.
Hypothesis X_TopSpace : TopSpace X XOpen.
Hypothesis Y_TopSpace : TopSpace Y YOpen.
Variable f : X -> Y.
Hypothesis f_Continuous : Continuous X XOpen Y YOpen f.
Variable U : Subset X.
Hypothesis U_Connected : Connected X XOpen U.

Instance image_Connected : Connected Y YOpen (image f U).
Proof.
  apply Build_Connected.
  apply Y_TopSpace.
  intros.
  destruct H2.
  destruct H3.
  assert (exists x : X, (intsec U (intsec (preimage f U1) (preimage f U2)) x)).
  apply Conn_insep.
  apply f_Continuous.
  apply H.
  apply f_Continuous.
  apply H0.
  assert (incl U (preimage f (image f U))).
  apply im_preim.
  assert (incl (preimage f (image f U)) (preimage f (union U1 U2))).
  apply preim_incl.
  apply H1.
  assert (preimage f (union U1 U2) = union (preimage f U1) (preimage f U2)).
  apply preim_union.
  rewrite <- H6.
  apply (incl_trans U (preimage f (image f U)) (preimage f (union U1 U2))).
  apply H4.
  apply H5.
  apply intsec_and in H2.
  unfold image in H2.
  destruct H2.
  destruct H2.
  exists x1.
  apply intsec_and.
  intuition.
  unfold preimage.
  subst.
  apply H4.
  apply intsec_and in H3.
  unfold image in H3.
  destruct H3.
  destruct H3.
  exists x1.
  apply intsec_and.
  intuition.
  unfold preimage.
  subst.
  apply H4.
  destruct H4.
  exists (f x1).
  apply intsec_and.
  apply intsec_and in H4.
  destruct H4.
  apply intsec_and in H5.
  unfold preimage in H5.
  split.
  unfold image.
  exists x1.
  intuition.
  apply intsec_and.
  apply H5.
Qed.

