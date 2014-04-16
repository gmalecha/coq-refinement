Require Import Coq.Setoids.Setoid.
Require Import ELRefine.Refinement.

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

Theorem plusParity_plus
: hrespectful Abstracts (hrespectful Abstracts Abstracts) plusParity plus.
Proof.
  repeat red; intros.
  induction H; simpl; intros; try solve [ repeat constructor ].
  { destruct x0; assumption. }
  { rewrite Abstracts_S.
    constructor. destruct x0; assumption. }
  { rewrite <- Abstracts_SS. assumption. }
Qed.
