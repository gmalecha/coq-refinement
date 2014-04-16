Require Import Refinement.

Section anti_framing.
  Variable T : Type.
  Variable P : T -> Prop.

  Inductive Rel : T -> T -> Prop :=
  | RP : forall t, P t -> Rel t t.

  Variable F : T -> T.

  Eval compute in hrespectful Rel Rel F F.
End anti_framing.