Require Import ELRefine.Refinement.
Require Import ELRefine.Relations.

Inductive typ : Type :=
| tyNat
| tyBool.

Definition typD (t : typ) : Type :=
  match t with
    | tyNat => nat
    | tyBool => bool
  end.

Inductive expr : typ -> Type :=
| Plus : expr tyNat -> expr tyNat -> expr tyNat
| Const : forall T, typD T -> expr T
| If : forall T, expr tyBool -> expr T -> expr T -> expr T.

Inductive eexpr : Type :=
| EPlus : eexpr -> eexpr -> eexpr
| ENat : nat -> eexpr
| EBool : bool -> eexpr
| EIf : eexpr -> eexpr -> eexpr -> eexpr.

Fixpoint eval {t : typ} (e : expr t) : typD t :=
  match e in expr t return typD t with
    | Plus a b => eval a + eval b
    | Const t x => x
    | If t a b c => if eval a then eval b else eval c
  end.

Fixpoint eeval (t : typ) (e : eexpr) : option (typD t) :=
  match e with
    | ENat n => match t with
                  | tyNat => Some n
                  | _ => None
                end
    | EBool b => match t with
                   | tyBool => Some b
                   | _ => None
                 end
    | EPlus a b => match t with
                     | tyNat =>
                       match eeval tyNat a
                           , eeval tyNat b
                       with
                         | Some x , Some y => Some (x + y)
                         | _ , _ => None
                       end
                     | _ => None
                   end
    | EIf t' a b =>
      match eeval tyBool t' with
        | Some true => eeval t a
        | Some false => eeval t b
        | None => None
      end
  end.

Inductive Erases : forall ty, eexpr -> expr ty -> Type :=
| Erases_Nat : forall n, Erases tyNat (ENat n) (Const tyNat n)
| Erases_Bool : forall n, Erases tyBool (EBool n) (Const tyBool n)
| Erases_Plus : forall a b a' b',
                  Erases tyNat a a' ->
                  Erases tyNat b b' ->
                  Erases tyNat (EPlus a b) (Plus a' b')
| Erases_If : forall t a b c a' b' c',
                Erases tyBool a a' ->
                Erases t b b' ->
                Erases t c c' ->
                Erases t (EIf a b c) (If t a' b' c').

Inductive Inj_option {T : Type} (x : T) : option T -> Type :=
| Inj_opt : @Inj_option T x (Some x).

Goal @hdrespectful _ _
     (fun x => expr x -> typD x)
     (fun y => eexpr -> option (typD y))
     (@id typ)
     (fun x y x_eq_y =>
        @hrespectful (expr x) eexpr _ _ (flip (@Erases x))
        match x_eq_y in @id _ _ t
              return hrelation (typD x) (option (typD t))
        with
          | refl =>  (@Inj_option _)
        end) (@eval) (@eeval).
Proof.
  red. destruct pf.
  red. intros.
  red in X. induction X.
  { simpl; constructor. }
  { simpl; constructor. }
  { simpl. destruct IHX1; destruct IHX2. constructor. }
  { simpl. destruct IHX1; destruct IHX2; destruct IHX3.
    destruct (eval a'); constructor. }
Qed.