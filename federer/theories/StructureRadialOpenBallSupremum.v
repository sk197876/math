(** Federer (1969), 3.3.4, p. 291:
    identify the actual unnormalized psi_v
    open-ball value with its literal original
    radius supremum. The numerator may be
    infinite and has no regularity premise. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealBoundsUP ExtendedRealBounds
  PositiveScalarExtendedSupremum StructureRadialImageMeasure StructureOpenBallGrowth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_radial_open_ball_supremum]:
    psi_v[B(z,t)] t^(-m) is exactly
    the original supremum over 0<r<1/v
    with both radius and aperture weights,
    Federer 3.3.4, p. 291. Original
    source sets, strict balls and the
    actual direction-map domain are retained. *)
Theorem structure_radial_open_ball_supremum (R:realType) (X Y:metricType R)
    m (phi:set X->\bar R) (A D:set X) (a:X) (f:X->Y)
    (delta t:R) (z:Y):0<t ->
  structure_open_ball_growth m
    (structure_radial_image_measure m phi A a D f delta) z t=
  extended_real_sup [set v|exists r:R,0<r<delta /\
    v=(phi [set x|A x /\ (mdist a x<r)%R /\ D x /\ (mdist z (f x)<t)%R]*
      ((r^-1)^+m)%:E*((t^-1)^+m)%:E)%E].
Proof.
move=>ht.
pose S:set Y:=[set y|mdist z y<t].
pose V:=[set v|exists r:R,0<r<delta /\
  v=structure_radial_image_component m phi A a D f r S].
have hRadius:structure_radial_image_measure m phi A a D f delta S=extended_real_sup V.
  have hS:is_extended_real_supremum V (extended_real_sup V).
    constructor; [exact:extended_real_sup_upper|exact:extended_real_sup_least].
  exact:(extended_real_supremum_unique
    (structure_radial_image_measure_specification m phi A a D f delta S) hS).
have hWeight:0<(t^-1)^+m by rewrite exprn_gt0 // invr_gt0.
rewrite /structure_open_ball_growth -/S hRadius muleC -extended_real_sup_positive_scalar //.
congr (extended_real_sup _); apply/seteqP; split=>v.
- move=>[b [r [hr ->]] <-]; exists r; split=>//.
  by rewrite /structure_radial_image_component /S [(_*phi _)%E]muleC muleC.
- move=>[r [hr ->]].
  exists (structure_radial_image_component m phi A a D f r S).
  + by exists r.
  + by rewrite /structure_radial_image_component /S [(_*phi _)%E]muleC muleC.
Qed.
