Require Import Setoid.

(** The abstract domain **)
Inductive Parity := Even | Odd.

(** The Abstraction Relation **)
Inductive Abstracts : Parity -> nat -> Prop :=
| A_Even : Abstracts Even 0
| A_Odd : Abstracts Odd 1
| A_SS : forall n p, Abstracts p n -> Abstracts p (2 + n).

(** Plus on the abstract domain **)
Definition plusParity (a b : Parity) : Parity :=
  match a , b with
    | Even , Odd
    | Odd , Even => Odd
    | _ , _ => Even
  end.

(** Lemmas **)
Definition opp (p : Parity) : Parity :=
  match p with
    | Even => Odd
    | Odd => Even
  end.

Lemma Abstracts_SS : forall n p, Abstracts p n <-> Abstracts p (S (S n)).
Proof.
  intros.
  destruct n; intuition; repeat constructor; auto.
  inversion H; auto.
  inversion H. auto.
Qed.

Theorem Abstracts_S : forall n p, Abstracts p n <-> Abstracts (opp p) (S n).
Proof.
  induction n.
  { intros. split. inversion 1. subst. constructor.
    destruct p; simpl; try constructor. inversion 1. }
  { intros.
    rewrite <- Abstracts_SS.
    specialize (IHn (opp p)); symmetry.
    destruct p; auto. }
Qed.

Goal forall a aA b bA,
       Abstracts aA a ->
       Abstracts bA b ->
       Abstracts (plusParity aA bA) (plus a b).
Proof.
  induction 1; simpl; intros.
  { destruct bA; assumption. }
  { destruct bA.
    { change Odd with (opp Even). rewrite Abstracts_S.
      constructor. apply H. }
    { change Even with (opp Odd). rewrite Abstracts_S.
      constructor. apply H. } }
  { constructor. auto. }
Qed.
