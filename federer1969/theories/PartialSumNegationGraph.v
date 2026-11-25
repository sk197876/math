(** Federer (1969), proof of 2.4.4(4), p. 83: negation turns addition of
    lower integral bounds into the upper-integral subadditivity argument.
    The scalar and graph identities below retain undefined opposite-infinity
    pairs. Source context: MeasureIntegralSqueeze.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal topology.
From Federer Require Import ExtendedRealPartial ExtendedRealOrderTopology PartialFunctionUP
  PartialFunctionPostcomposition PartialExtendedArithmetic MeasureIntegralNegation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ereal_scope.

(** Source for [extended_add_negated_sum]: supporting defined-
    sum negation identity used in Federer 2.4.4(4), p. 83. *)
Lemma extended_add_negated_sum (R : realType) (a b z : \bar R) :
  extended_add a b=Some z -> extended_add (-a) (-b)=Some (-z).
Proof.
rewrite /extended_add; case hd : (adde_def a b)=> // => -[<-].
by rewrite adde_defNN hd oppeD.
Qed.

(** Source for [partial_extended_sum_negation_graph]: supporting
    exact identity -(f+g)=(-f)+(-g) in the proof of Federer
    2.4.4(4), p. 83. Both graphs exclude opposite infinities. *)
Lemma partial_extended_sum_negation_graph (R : realType) (X : Type)
    (f g : partial_function X (extended_real_line R)) x z :
  partial_function_graph (partial_extended_function_negate (partial_extended_function_add f g)) x z <->
  partial_function_graph (partial_extended_function_add (partial_extended_function_negate f)
    (partial_extended_function_negate g)) x z.
Proof.
split.
- move=> [y [hy he]].
  have [a [b [ha [hb hab]]]] := (@partial_extended_function_add_graph R X f g x y).1 hy.
  apply/partial_extended_function_add_graph; exists (-a),(-b); split.
  + exists a; by split.
  split; first by exists b; split.
  rewrite -he; exact: extended_add_negated_sum hab.
- move=> hz; have [a [b [[u [hu hua]] [[v [hv hvb]] hab]]]] :=
    (@partial_extended_function_add_graph R X _ _ x z).1 hz.
  have hh := extended_add_negated_sum hab.
  rewrite -hua -hvb !oppeK in hh.
  exists (-z); split; last exact: oppeK.
  apply/partial_extended_function_add_graph; exists u,v; by split=> //; split.
Qed.
