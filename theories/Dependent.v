Require Import Refinement.

(** Example of dependent refinement **)
Definition denote (b : bool) : Type :=
  match b with
    | true => nat
    | false => bool
  end.

Definition denote' (b : bool) : Type :=
  match b with
    | true => bool
    | false => nat
  end.

Inductive relD : hrelation bool bool :=
| relD_tf : relD true false
| relD_ft : relD false true.

Definition denoteD a b (pf : relD a b) : hrelation (denote a) (denote' b) :=
  match pf in relD a b return hrelation (denote a) (denote' b) with
    | relD_tf => eq
    | relD_ft => eq
  end.

Definition default (a : bool) : denote a :=
  match a as a return denote a with
    | true => 0
    | false => false
  end.

Definition default' (a : bool) : denote' a :=
  match a as a return denote' a with
    | true => false
    | false => 0
  end.

Theorem default_default' : hdrespectful _ denoteD default default'.
Proof.
  repeat red; intros.
  destruct pf; reflexivity.
Qed.