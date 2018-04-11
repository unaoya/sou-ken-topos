Definition Subset (X : Set) : Type := X -> Prop.
Definition single : Set -> Prop :=
  fun X : Set => forall x y : X, x = y.
Definition empty (X : Set) : Subset X := fun (x : X) => x <> x.
Inductive incl {X : Set} : Subset X -> Subset X -> Prop :=
    | Incl_intro : forall S1 S2 : Subset X,
                   (forall x : X, S1 x -> S2 x) ->
                   incl S1 S2.
Definition identity (E : Set) : E -> E := fun x : E => x.
Definition comp {A B C : Set} (g:B -> C) (f:A -> B) : A -> C := fun a : A => g (f a).

Variable X : Set.
Variable F : Subset X -> Set.
Variable res : forall U V : Subset X, F U -> F V.

Hypothesis empty_single : single (F (empty X)).
Hypothesis res_id : forall (U : Subset X) (u : F U), (res U U) u = identity (F U) u.
Hypothesis res_trans : forall U V W : Subset X, res U W = comp (res V W) (res U V).

Lemma empty_unique : forall (U V : Subset X) (a : F U) (b : F V), res U (empty X) a = res V (empty X) b.
Proof.
  intros.
  apply empty_single.
Qed.

Hypothesis A_eq_comm : forall (A : Set) (a b : A), a = b -> b = a.
  
Lemma E_domain : forall (U : Subset X) (a : F U), res U U a = a.
Proof.
  intros.
  assert (res U U a = identity (F U) a).
  apply res_id.
  apply H.
Qed.

Definition intsec {X : Set} (U V : Subset X) : Subset X :=
  fun (x : X) => U x /\ V x.

Lemma r_trans : forall (U V W : Subset X) (a : F U), res V W (res U V a) = res U W a.
Proof.
  intros.
  assert (res U W = comp (res V W) (res U V)).
  apply res_trans.
  assert (res U W a = comp (res V W) (res U V) a).
  rewrite H.
  auto.
  unfold comp in H0.
  rewrite H0.
auto.
Qed.  
            
(*
Definition A : Set.
Definition E : A -> Subset X.
Definition r : A -> Subset X -> A.
*)
