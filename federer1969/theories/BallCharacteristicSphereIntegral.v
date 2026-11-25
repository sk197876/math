(** Federer (1969), 3.2.13, p. 250: apply
    polar integration to the unit-ball characteristic
    function. On a unit sphere, its
    radius-r evaluation is one for r<1
    and zero otherwise, without a finite sphere-mass premise. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerNormInequalities InnerMetric
  SphereConstantIntegral PolarUnitSphereIntegral HausdorffMeasure CharacteristicFunctionUP
  PartialFunctionUP PartialFunctionPrecomposition PartialZeroExtension MeasureIntegralGraphEquivalence SummableRealFunctionUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [unit_ball_characteristic_on_dilated_sphere]: the
    unit-ball characteristic function becomes the radius
    cutoff on the unit sphere, in the
    normalization argument of Federer 3.2.13, p. 250. *)
Lemma unit_ball_characteristic_on_dilated_sphere (R:realType) m (g:R_n R m->R) (r:R):
  is_characteristic_function [set x|(inner_norm (@euclidean_inner_productP R m) x<1)%R] g ->
  (0<r)%R ->forall x,inner_norm (@euclidean_inner_productP R m) x= 1%R ->
    g (r*:x)=(if (r<1)%R then 1%R else 0%R).
Proof.
move=>hg hr x hx.
have hN:inner_norm (@euclidean_inner_productP R m) (r*:x)=r.
  by rewrite inner_normZ (gtr0_norm hr) hx mulr1.
case:ifP=>hr1.
- apply:(characteristic_on_set hg); change (is_true ((inner_norm (@euclidean_inner_productP R m) (r*:x)<1)%R)); by rewrite hN.
- apply:(characteristic_off_set hg)=>h.
  have hLt:(r<1)%R.
    change (is_true ((inner_norm (@euclidean_inner_productP R m) (r*:x)<1)%R)) in h.
    by rewrite hN in h.
  by move:hr1; rewrite hLt.
Qed.

(** Source for [unit_ball_characteristic_unit_sphere_integral]: the
    actual unit-sphere inner integral for the
    unit-ball test in Federer 3.2.13,
    p. 250. Its value is the
    sphere mass for 0<r<1 and zero
    for r>= 1; infinite sphere mass is permitted here. *)
Lemma unit_ball_characteristic_unit_sphere_integral (R:realType) m
    (g:R_n R m->R) (r:R):
  is_characteristic_function [set x|(inner_norm (@euclidean_inner_productP R m) x<1)%R] g ->
  (0<r)%R ->partial_function_graph (unit_sphere_dilation_integral (real_total_integrand g)) r
    ((if (r<1)%R then 1%R else 0%R)%:E*
      @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) (m-1)
        [set x|inner_norm (@euclidean_inner_productP R m) x= 1%R]).
Proof.
move=>hg hr; apply/unit_sphere_dilation_integral_graph.
have hc:(0<=((if (r<1)%R then 1%R else 0%R):R))%R by case:ifP=>h; [exact:ler01|exact:lexx].
have hI:=@sphere_constant_subset_integral R m (m-1) 1%R
  (if (r<1)%R then 1%R else 0%R) (fun x=>g (r*:x)) hc
  (@unit_ball_characteristic_on_dilated_sphere R m g r hg hr).
apply:MeasureIntegralGraphEquivalence.measure_integral_graph_equivalent _ hI=>x z.
rewrite !PartialZeroExtension.partial_function_zero_extension_graph !real_total_integrand_graph.
by [].
Qed.
