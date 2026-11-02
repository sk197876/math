(** Federer (1969), 2.10.25, pp. 188–189: supporting null-image and
    zero-Lipschitz-bound cases. Outside the image of A the fibre is empty.
    If that image is target-Hausdorff null, the fibre-mass function is
    almost everywhere zero, even when its exceptional values are infinite.
    The already proved image bound 2.10.11, p. 176, handles zero Lipschitz
    bounds in positive target degree. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic LipschitzUP
  HausdorffMeasure HausdorffLipschitzImages MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  MeasureConullZeroIntegral MeasureIntegralBounds MeasureIntegralUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [hausdorff_fibre_integral_null_image]: supporting
    null-image boundary of 2.10.25, pp. 188–189.
    The fibre masses may be infinite on the null
    image. No measurability of A or of the
    original fibre-mass function is assumed. *)
Theorem hausdorff_fibre_integral_null_image (R : realType) (X Y : metricType R)
    (f : X -> Y) (k m : nat) (A : set X) :
  @hausdorff_measure R Y m (f @` A)=0 ->
  measure_upper_integral (@hausdorff_measure R Y m)
    (partial_function_total (fun y=>(@hausdorff_measure R X k (A `&` f @^-1` [set y]) : extended_real_line R)))=0.
Proof.
move=> hnull.
pose mu := @hausdorff_measure R Y m.
have hm : is_measure mu := @hausdorff_measure_is_measure R Y m.
pose g (y : Y) := (@hausdorff_measure R X k (A `&` f @^-1` [set y]) : extended_real_line R).
have hoff : measure_almost_everywhere mu (~` (f @` A)) by rewrite /measure_almost_everywhere setCK.
have hae : measure_almost_everywhere mu [set y | partial_function_graph (partial_function_total g) y 0].
  apply: (@measure_almost_everywhere_mono R Y mu hm _ _ _ hoff)=> y hy.
  have he : A `&` f @^-1` [set y]=set0.
    apply/seteqP; split=> [x [hx hxy]|x []]; exfalso; apply: hy; by exists x.
  change (g y=0); rewrite /g he; exact: measure_empty (@hausdorff_measure_is_measure R X k).
have hi := @measure_almost_zero_integral R Y mu hm (partial_function_total g) hae.
exact: (@measure_upper_integral_unique R Y mu _ _ 0 (measure_upper_integral_specification mu _) hi.2.1).
Qed.

(** Source for [zero_lipschitz_positive_degree_fibre_integral_zero]:
    supporting zero-bound case of 2.10.25, pp. 188–189.
    Apply the proved Hausdorff image comparison of
    2.10.11, p. 176, before the null-image lemma.
    Infinite source mass still gives zero by the
    book's zero-times-infinity convention. *)
Theorem zero_lipschitz_positive_degree_fibre_integral_zero (R : realType) (X Y : metricType R)
    (f : X -> Y) (k m : nat) (A : set X) :
  is_metric_lipschitz_bound setT f 0%R -> (0<m)%N ->
  measure_upper_integral (@hausdorff_measure R Y m)
    (partial_function_total (fun y=>(@hausdorff_measure R X k (A `&` f @^-1` [set y]) : extended_real_line R)))=0.
Proof.
move=> hf hm.
have hh := @hausdorff_lipschitz_image_bound R X Y f 0%R m hf A.
have hmne : m!=0%N by rewrite -lt0n.
rewrite expr0n (negbTE hmne) mul0e in hh.
have hz : @hausdorff_measure R Y m (f @` A)=0.
  apply/eqP; by rewrite eq_le hh (measure_nonnegative (@hausdorff_measure_is_measure R Y m)).
exact: hausdorff_fibre_integral_null_image hz.
Qed.
