(** Federer (1969), 3.1.20, p. 232: compatible class-k formulas
    on open pieces glue to a class-k map on their union. Existence
    is established from class locality, without prescribing a public
    choice of values outside the union. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP NormRegularity NormRegularityOperations NormRegularityLocal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [norm_class_compatible_gluing]: supporting the
    three-piece definition of f_i in Federer 3.1.20, p. 232.
    Two class-k maps agreeing on the overlap have a class-k gluing
    on the union, with both exact restriction equations. *)
Lemma norm_class_compatible_gluing (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A B:X->Prop) (f g:X->Y) k :
  norm_class hNX hNY A f k -> norm_class hNX hNY B g k ->
  (forall x, A x -> B x -> f x=g x) ->
  exists h:X->Y, norm_class hNX hNY (fun x=>A x \/ B x) h k /\
    (forall x, A x -> h x=f x) /\ (forall x, B x -> h x=g x).
Proof.
move=>hf hg hfg.
pose h:=fun x=>if `[<A x>] then f x else g x.
have hA x (hx:A x):h x=f x by rewrite /h (asboolT hx).
have hB x (hx:B x):h x=g x.
  rewrite /h; case:asboolP=>[ha|ha]=>//; exact: hfg ha hx.
exists h; split; last by split.
apply: norm_class_local=>a [ha|ha].
- exists A; split=>//; split; first by move=>x hx; left.
  exact: norm_class_domain_agreement (fun x hx=>esym (hA x hx)) hf.
- exists B; split=>//; split; first by move=>x hx; right.
  exact: norm_class_domain_agreement (fun x hx=>esym (hB x hx)) hg.
Qed.
