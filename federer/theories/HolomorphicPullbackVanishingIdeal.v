(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.8(2),(10), pp. 326, 332–333:
    actual holomorphic pullback transports the
    vanishing ideal of an original set.
    Use the public all-representative pullback
    and local-vanishing equations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed RealNormUP NormMetric HolomorphicGermRepresentatives HolomorphicGermUP HolomorphicGermRing
  HolomorphicGermRingLaws PointedHolomorphicPullbackUP SetGermUP HolomorphicGermVanishingSealed HolomorphicGermVanishingRepresentative
  VanishingNearHomeomorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_pullback_vanishing_ideal_membership]:
    alpha vanishes on S if and
    only if its actual holomorphic pullback
    vanishes on u inverse(S), supporting
    3.4.12, p. 339, extending 3.4.8(10), pp. 332–333.
    No ideal or variety correspondence is assumed. *)
Theorem holomorphic_pullback_vanishing_ideal_membership (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) a (u v:X->X)
    (M:{rmorphism [the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)]->
      [the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)]}):
  is_pointed_holomorphic_germ_pullback u M ->
  continuous (fun x:real_norm_metric_space hNX=>(u x:real_norm_metric_space hNX)) ->
  continuous (fun x:real_norm_metric_space hNX=>(v x:real_norm_metric_space hNX)) ->
  u a=a ->v a=a ->cancel u v ->cancel v u ->
  forall (S:set X) (alpha:[the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)]),
    @HolomorphicSetIdeal.value R X NX hNX a
      (@set_germ (Topological.clone (real_norm_metric_space hNX) _) a S) alpha <->
    @HolomorphicSetIdeal.value R X NX hNX a
      (@set_germ (Topological.clone (real_norm_metric_space hNX) _) a (u @^-1` S)) (M alpha).
Proof.
move=>hM hU hV hUA hVA hUV hVU S alpha.
have [f hF]:=@holomorphic_germ_has_representative R X NX hNX a alpha.
have [g [hG hValues]]:=hM f.
rewrite -hF hG !holomorphic_set_ideal_representative_equation.
exact:(@vanishing_near_homeomorphism (Topological.clone (real_norm_metric_space hNX) _)
  [the zmodType of (ComplexScalars.C R)^o] u v a S (holomorphic_representative_value f) (holomorphic_representative_value g)
  hU hV hUA hVA hUV hVU hValues).
Qed.
