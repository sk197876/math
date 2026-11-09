(** Federer (1969), 3.3.4, p. 288: the zero
    plane satisfies the ordinary zero-growth alternative,
    with no assumption on the original source. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations GrassmannSubspaces ModuleQuotient
  EuclideanInnerProduct InnerMetric StructureCone StructurePlaneGrowth StructureZeroPlaneCone
  StructureConeDensityValues MeasureUP MeasureBasic ExtendedRealBounds
  PositiveRightOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_zero_plane_radial_zero]: the
    exact radius supremum in Federer 3.3.4(1),
    p. 288, is zero for the zero plane at
    every aperture in (0,1], including infinite outer
    measures and arbitrary original source sets. *)
Lemma structure_zero_plane_radial_zero (R:realType) n m
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n))) a
    (V:G (R_n R n) 0) (delta s:R):
  is_measure phi ->0<delta ->0<s ->s<=1 ->
  structure_plane_radial_supremum m phi A a V delta s=0%E.
Proof.
move=>hPhi hd hs hs1.
have hEmpty r:A `&` structure_cone V a r s=set0.
  by rewrite (structure_zero_plane_cone_empty V a r hs hs1) setI0.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply:extended_real_sup_least=>z [r [hr ->]].
  by rewrite hEmpty (measure_empty hPhi) !mul0e.
- have hr:=structure_density_positive_half_bounds hd.
  have hValue:(0: \bar R)=
      (phi (A `&` structure_cone V a (delta/2)%:E s)*
        (((delta/2)^-1)^+m)%:E*((s^-1)^+m)%:E)%E.
    by rewrite hEmpty (measure_empty hPhi) !mul0e.
  apply:extended_real_sup_upper; exists (delta/2); by split.
Qed.

(** Source for [structure_zero_plane_zero_growth]: the
    n=m endpoint of Federer 3.3.4, p. 288,
    satisfies (1) pointwise, without a measurability
    or finiteness hypothesis on A or on phi(A). *)
Theorem structure_zero_plane_zero_growth (R:realType) n m
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n))) a
    (V:G (R_n R n) 0):
  is_measure phi ->structure_plane_zero_growth m phi A a V.
Proof.
move=>hPhi; exists 1; split; first exact:ltr01.
have hZero s (hs:0<s) (hs1:s<1):
    structure_plane_radial_supremum m phi A a V 1 s=0%E.
  exact:(@structure_zero_plane_radial_zero R n m phi A a V 1 s
    hPhi ltr01 hs (ltW hs1)).
split.
- move=>b hb; exists 1; split; first exact:ltr01.
  by move=>s hs hs1; rewrite (hZero s hs hs1).
- move=>b hb; exists 1; split; first exact:ltr01.
  by move=>s hs hs1; rewrite (hZero s hs hs1).
Qed.
