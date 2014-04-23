Require Import ELRefine.Refinement.

Definition flip {A B : Type} (R : hrelation A B) : hrelation B A :=
  fun a b => R b a.

Inductive id {T : Type} (x : T) : T -> Type :=
| refl : @id _ x x.
