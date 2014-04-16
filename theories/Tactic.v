Require Import Refinement.

Create HintDb refinements. (** this should be discriminated **)

Ltac unify a b :=
  let z := constr:(@eq_refl _ a : a = b) in
  idtac.

Ltac otherwise_assumption pf :=
  try match goal with
        | P : _ |- _ =>
          first [ match eval cbv delta [ P ] in P with
                    | ?Z => is_evar Z ; fail 2
                    | _ => unify pf P
                  end
                | unify pf P
                ]
      end.

Ltac solve_refinement otherwise :=
  let rec solve_refinement' R a b pf :=
      match a with
        | ?af ?ax =>
          match b with
            | ?bf ?bx =>
              (match type of af with
                 | ?A -> ?B =>
                   match type of bf with
                     | ?C -> ?D =>
                       (** TODO: There is an issue with ordering and the
                        ** scope of unification variables!
                        **)
                       (let Rab := fresh in
                        evar (Rab : hrelation A C) ;
                        let Rab' := eval cbv delta [ Rab ] in Rab in
                        let R' := constr:(@hrespectful A C B D Rab' R) in
                        let pfF := fresh in
                        evar (pfF : R' af bf) ;
                        let pfF' := eval cbv delta [ pfF ] in pfF in
                        solve_refinement' R' af bf pfF' ;
                        let pfX := fresh in
                        evar (pfX : Rab' ax bx) ;
                        let pfX' := eval cbv delta [ pfX ] in pfX in
                        solve_refinement' Rab' ax bx pfX' ;
                        unify pf (@App_simple A C B D Rab R af bf ax bx pfF pfX))
                     | _ => otherwise pf
                   end
                 | forall x : ?A , @?F x =>
                   match type of bf with
                     | forall x : ?C , @?G x =>
                       (let Rac := fresh in
                        evar (Rac : hrelation A C) ;
                        let Rac' := eval cbv delta [ Rac ] in Rac in
                        let pfX := fresh in
                        evar (pfX : Rac' ax bx) ;
                        let pfX' := eval cbv delta [ pfX ] in pfX in
                        solve_refinement' Rac' ax bx pfX ;
                        let Rfg := fresh in
                        evar (Rfg : forall (a : A) (b : C),
                                      Rac' a b ->
                                      hrelation (F a) (G b)) ;
                        let Rfg' := eval cbv delta [ Rfg ] in Rfg in
                        let pfF := fresh in
                        let R' := constr:(@hdrespectful A C F G Rac' Rfg') in
                        evar (pfF : R' af bf) ;
                        let pfF' := eval cbv delta [ pfF ] in pfF in
                        solve_refinement' R' af bf pfF ;
                        unify pf (@App_dep A C F G Rac Rfg af bf ax bx pfF pfX))
                     | _ => otherwise pf
                   end
               end)
            | _ => otherwise pf
          end
        | _ => otherwise pf
      end
  in
  match goal with
    | |- ?X ?A ?B =>
      let H := fresh in
      evar (H : X A B) ;
      let H' := eval cbv delta [ H ] in H in
      solve_refinement' X A B H' ;
      exact H
  end.

Section problem.
  Context {A B E F : Type}.
  Variable f : A -> B.
  Variable g : E -> F.
  Variables (Rae : hrelation A E)
            (Rbf : hrelation B F).
  Hypothesis H' : (hrespectful Rae Rbf) f g.

  Goal forall a x, Rae a x ->
         Rbf (f a) (g x).
  intros.
  solve_refinement otherwise_assumption.
  Defined.
End problem.

Section problem_big.
  Context {A B C D E F G H : Type}.
  Variable f : A -> B -> C -> D.
  Variable g : E -> F -> G -> H.
  Variables (Rae : hrelation A E)
            (Rbf : hrelation B F)
            (Rcg : hrelation C G)
            (Rdh : hrelation D H).
  Hypothesis H' : (hrespectful Rae (hrespectful Rbf (hrespectful Rcg Rdh))) f g.

  Goal forall a b c x y z,
         Rdh (f a b c) (g x y z).
  intros.
  solve_refinement otherwise_assumption.
  Grab Existential Variables.
  admit. admit. admit.
  Defined.
End problem_big.