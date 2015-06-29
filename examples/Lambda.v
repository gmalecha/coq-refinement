Require Import Coq.Lists.List.
Require Import Coq.Relations.Relations.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Eqdep_dec.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Member.
Require Import ExtLib.Data.HList.

Set Implicit Arguments.
Set Strict Implict.

Inductive typ : Type := Nat | Arr (dom codom : typ).

Fixpoint typD (t : typ) : Type :=
  match t with
  | Nat => nat
  | Arr a b => typD a -> typD b
  end.

Inductive wt_expr (vs : list typ) : typ -> Type :=
| wtApp : forall t1 t2, wt_expr vs (Arr t1 t2) -> wt_expr vs t1 -> wt_expr vs t2
| wtAbs : forall t1 t2, wt_expr (t1 :: vs) t2 -> wt_expr vs (Arr t1 t2)
| wtVar : forall t, member t vs -> wt_expr vs t
| wtConst : forall t, typD t -> wt_expr vs t.

Inductive expr : Type :=
| App (f x : expr)
| Abs : typ -> expr -> expr
| Var : nat -> expr
| Const : forall t, typD t -> expr.

Fixpoint erase vs t (e : wt_expr vs t) : expr :=
  match e with
  | wtApp a b => App (erase a) (erase b)
  | @wtAbs _ t _ a => Abs t (erase a)
  | @wtVar _ _ m => Var (to_nat m)
  | @wtConst _ t x => @Const t x
  end.

Definition wt_expr_expr' vs t (wt : wt_expr vs t) (e : expr) : Prop :=
  erase wt = e.

Inductive wt_expr_expr vs : forall t, wt_expr vs t -> expr -> Prop :=
| rApp : forall t1 t2 e1 e1' e2 e2',
    @wt_expr_expr vs (Arr t1 t2) e1 e1' ->
    @wt_expr_expr vs t1 e2 e2' ->
    @wt_expr_expr vs t2 (wtApp e1 e2) (App e1' e2')
| rAbs : forall t1 t2 e1 e1',
    @wt_expr_expr (t1 :: vs) t2 e1 e1' ->
    @wt_expr_expr vs (Arr t1 t2) (wtAbs e1) (Abs t1 e1')
| rVar : forall t (m : member t vs),
    @wt_expr_expr vs t (wtVar m) (Var (to_nat m))
| rConst : forall t v,
    @wt_expr_expr vs t (wtConst vs t v) (Const t v).

Fixpoint wt_exprD vs t (e : wt_expr vs t) : hlist typD vs -> typD t :=
  match e in wt_expr _ t return hlist typD vs -> typD t with
  | wtApp a b =>
    let aD := @wt_exprD _ _ a in
    let bD := @wt_exprD _ _ b in
    fun x => (aD x) (bD x)
  | @wtAbs _ _ t e =>
    let eD := @wt_exprD _ _ e in
    fun x => fun y => eD (Hcons y x)
  | wtVar m => fun x => hlist_get m x
  | wtConst _ _ x => fun _ => x
  end.

Definition type_eq (a b : typ) : {a = b} + {a <> b}.
decide equality.
Defined.

Fixpoint type_of_expr (vs : list typ) (e : expr) : option typ :=
  match e with
  | App a b =>
    match type_of_expr vs a , type_of_expr vs b with
    | Some (Arr ta tb) , Some ta' =>
      if type_eq ta ta' then Some tb else None
    | _ , _ => None
    end
  | Abs t e =>
    match type_of_expr (t :: vs) e with
    | Some t' => Some (Arr t t')
    | _ => None
    end
  | Var v => nth_error vs v
  | Const t _ => Some t
  end.

Fixpoint exprD vs t (e : expr) : option (hlist typD vs -> typD t) :=
  match e with
  | Abs _ e =>
    match t as t return option (hlist typD vs -> typD t) with
    | Arr t' r =>
      match exprD (t' :: vs) r e with
      | None => None
      | Some eD => Some (fun x y => eD (Hcons y x))
      end
    | _ => None
    end
  | App a b =>
    match type_of_expr vs b with
    | Some ta =>
      match exprD vs (Arr ta t) a , exprD vs ta b with
      | Some f , Some x => Some (fun vs => (f vs) (x vs))
      | _ , _ => None
      end
    | _ => None
    end
  | Var n =>
    match nth_error_get_hlist_nth typD vs n with
    | Some (existT _ t' get) =>
      match type_eq t' t with
      | left pf =>
        match pf in _ = X return option (hlist typD vs -> typD X) with
        | eq_refl => Some get
        end
      | right _ => None
      end
    | None => None
    end
  | Const t' val =>
    match type_eq t' t with
    | left pf =>
      match pf in _ = X return option (hlist typD vs -> typD X) with
      | eq_refl => Some (fun _ => val)
      end
    | _ => None
    end
  end.

Inductive Succeeds {T U : Type} (rT : T -> U -> Prop) : T -> option U -> Prop :=
| Success : forall x y, rT x y -> Succeeds rT x (Some y).

Lemma something : forall vs t (wte : wt_expr vs t) e,
    wt_expr_expr wte e ->
    type_of_expr vs e = Some t.
Proof.
  induction 1; simpl; auto.
  { rewrite IHwt_expr_expr1. rewrite IHwt_expr_expr2.
    destruct (type_eq t1 t1); auto. congruence. }
  { rewrite IHwt_expr_expr. reflexivity. }
  { induction m; simpl; try eauto. }
Qed.

Lemma K_eq_typ : forall (a b : typ) (pf1 pf2 : a = b), pf1 = pf2.
Proof.
  eapply UIP_dec.
  eapply type_eq.
Qed.

Goal forall vs t wte e,
    @wt_expr_expr vs t wte e ->
    Succeeds (eq ==> eq)%signature (@wt_exprD vs t wte) (@exprD vs t e).
Proof.
  induction 1; simpl; intros.
  { erewrite something by eauto.
    destruct IHwt_expr_expr1.
    destruct IHwt_expr_expr2.
    constructor. red. intros; subst.
    erewrite H2 by eauto.
    erewrite H1 by eauto.
    reflexivity. }
  { destruct IHwt_expr_expr.
    constructor. red. intros; subst.
    eapply FunctionalExtensionality.functional_extensionality.
    intros. eapply H0. reflexivity. }
  { induction m.
    { simpl.
      destruct (type_eq t t); try congruence.
      rewrite (eq_option_eq e (fun X => (hlist typD (t :: ls) -> typD X))).
      constructor.
      red. intros. subst.
      rewrite (eq_Arr_eq e).
      rewrite eq_Const_eq.
      generalize (hlist_hd y). clear.
      rewrite (K_eq_typ e eq_refl). reflexivity. }
    { simpl.
      destruct (nth_error_get_hlist_nth typD ls (to_nat m));
        try solve [ inversion IHm ].
      destruct s.
      destruct (type_eq x t); try solve [ inversion IHm ].
      subst. inversion IHm; clear IHm; subst.
      constructor. red. intros; subst.
      erewrite <- H1; reflexivity. } }
  { destruct (type_eq t t); try congruence.
    rewrite (K_eq_typ e eq_refl). constructor.
    reflexivity. }
Qed.