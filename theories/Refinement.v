Set Implicit Arguments.
Set Strict Implicit.

Section relation.
  Variable A B : Type.
  Definition hrelation := A -> B -> Type.
End relation.

Section respectful.
  Context {A B C D : Type}.
  Variable Rab : hrelation A B.
  Variable Rcd : hrelation C D.

  Definition hrespectful : hrelation (A -> C) (B -> D) :=
    fun f g =>
      forall x y, Rab x y -> Rcd (f x) (g y).

  Theorem App_simple
  : forall f g x y,
      hrespectful f g ->
      Rab x y ->
      Rcd (f x) (g y).
  Proof.
    intros. apply X. assumption.
  Defined.

End respectful.

Section drespectful.
  Context {A B : Type}.
  Context {F : A -> Type} {G : B -> Type}.

  Variable Rab : hrelation A B.
  Variable Rcd : forall a b, Rab a b -> hrelation (F a) (G b).

  Definition hdrespectful : hrelation (forall x : A, F x) (forall x : B, G x) :=
    fun f g =>
      forall x y (pf : Rab x y), Rcd pf (f x) (g y).

  Theorem App_dep
  : forall f g x y,
      hdrespectful f g ->
      forall pf : Rab x y,
        Rcd pf (f x) (g y).
  Proof.
    intros. apply X.
  Defined.

End drespectful.
