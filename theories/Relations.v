Require Import ELRefine.Refinement.

Set Implicit Arguments.
Set Strict Implicit.

Definition flip {A B : Type} (R : hrelation A B) : hrelation B A :=
  fun a b => R b a.

Inductive id {T : Type} (x : T) : T -> Type :=
| refl : @id _ x x.

Section compose.
  Context {T U V : Type}.
  Variable R : hrelation T U.
  Variable S : hrelation U V.

  Inductive compose (x : T) (z : V) : Type :=
  | Compose : forall y, R x y -> S y z -> compose x z.
End compose.

Section functional.
  Context {T U : Type}.
  Variable f : T -> U.

  Inductive functional (x : T) : U -> Type :=
  | Functional : functional x (f x).
End functional.