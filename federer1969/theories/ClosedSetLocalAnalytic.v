(** Federer (1969), 3.4.5, p. 321: a closed
    set locally defined by analytic equations at its own
    points is analytic in the whole ambient space. Its
    original complement supplies actual empty neighbourhoods. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric FiniteAnalyticVarietyUP FiniteAnalyticVarietyBoundary
  AnalyticVarietyGermUP AnalyticSetLocalCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [closed_set_local_analytic_suffices]: the
    open-cover form of local analyticity in 3.4.5, p. 321,
    applied to closed sets as in the cited example. Empty
    complement neighbourhoods are proved, rather than assumed. *)
Theorem closed_set_local_analytic_suffices (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (S:set X):
  @closed (real_norm_metric_space hNX) S ->
  (forall a,S a ->exists U:set X,U a /\is_finite_analytic_variety hNX U (U `&` S)) ->
  is_analytic_set_in hNX setT S.
Proof.
move=>hClosed hLocal.
apply/(analytic_set_local_cover_equivalence hNX setT S)=>a _.
case:(pselect (S a))=>[ha|ha];first exact:hLocal a ha.
pose U:set X:=~`S.
have hU:@open (real_norm_metric_space hNX) U:=closed_openC hClosed.
exists U;split;first exact:ha.
have hEmpty:U `&` S=set0.
  apply/seteqP;split;[by move=>x [hNo hYes];exact:hNo hYes|by move=>x hx;case:hx].
rewrite hEmpty;exact:(@finite_analytic_variety_domain_empty R X NX hNX U hU).
Qed.
