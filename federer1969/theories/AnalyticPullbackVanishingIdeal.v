(** Federer (1969), 3.4.8(2),(10), pp. 326, 332–333:
    actual analytic pullback transports the
    vanishing ideal of an original set.
    Use the public all-representative pullback
    and local-vanishing equations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric AnalyticGermRepresentatives AnalyticGermUP AnalyticGermRing
  AnalyticGermRingLaws PointedAnalyticPullbackUP SetGermUP GermVanishingSealed GermVanishingRepresentative
  VanishingNearHomeomorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [analytic_pullback_vanishing_ideal_membership]:
    alpha vanishes on S if and
    only if its actual analytic pullback
    vanishes on u inverse(S), supporting
    3.4.8(10), pp. 332–333.
    No ideal or variety correspondence is assumed. *)
Theorem analytic_pullback_vanishing_ideal_membership (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) a (u v:X->X)
    (M:{rmorphism [the comNzRingType of (@analytic_germ_ring R X NX hNX a)]->
      [the comNzRingType of (@analytic_germ_ring R X NX hNX a)]}):
  is_pointed_analytic_germ_pullback u M ->
  continuous (fun x:real_norm_metric_space hNX=>(u x:real_norm_metric_space hNX)) ->
  continuous (fun x:real_norm_metric_space hNX=>(v x:real_norm_metric_space hNX)) ->
  u a=a ->v a=a ->cancel u v ->cancel v u ->
  forall (S:set X) (alpha:[the comNzRingType of (@analytic_germ_ring R X NX hNX a)]),
    @AnalyticSetIdeal.value R X NX hNX a
      (@set_germ (Topological.clone (real_norm_metric_space hNX) _) a S) alpha <->
    @AnalyticSetIdeal.value R X NX hNX a
      (@set_germ (Topological.clone (real_norm_metric_space hNX) _) a (u @^-1` S)) (M alpha).
Proof.
move=>hM hU hV hUA hVA hUV hVU S alpha.
have [f hF]:=@analytic_germ_has_representative R X NX hNX a alpha.
have [g [hG hValues]]:=hM f.
rewrite -hF hG !analytic_set_ideal_representative_equation.
exact:(@vanishing_near_homeomorphism (Topological.clone (real_norm_metric_space hNX) _)
  [the zmodType of R^o] u v a S (analytic_representative_value f) (analytic_representative_value g)
  hU hV hUA hVA hUV hVU hValues).
Qed.
