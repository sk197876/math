(** Federer (1969), 3.2.13, p. 250: integrate
    a constant value on a norm sphere
    without first assuming its Hausdorff mass finite.
    This supports the deduction of sphere mass
    from the characteristic function of the unit ball. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HausdorffMeasure
  EuclideanSphereMeasurable CharacteristicFunctionUP CharacteristicFunctionSealed PartialFunctionUP PartialFunctionBasic
  PartialZeroExtension MeasureUP MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralGraphEquivalence
  MeasureExtendedCharacteristicIntegral SummableRealFunctionUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [sphere_constant_subset_integral]: a constant
    nonnegative value on a sphere integrates to
    that value times its Hausdorff mass, supporting
    the normalization in Federer 3.2.13, p. 250.
    The original real function is arbitrary outside
    the sphere, and the mass may be infinite. *)
Lemma sphere_constant_subset_integral (R:realType) m k (r c:R) (g:R_n R m->R):
  (0<=c)%R ->(forall x,inner_norm (@euclidean_inner_productP R m) x=r ->g x=c) ->
  is_measure_subset_integral (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) k)
    [set x|inner_norm (@euclidean_inner_productP R m) x=r] (real_total_integrand g)
    (c%:E* @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) k
      [set x|inner_norm (@euclidean_inner_productP R m) x=r]).
Proof.
move=>hc hg.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose H:=@hausdorff_measure R X k.
pose S:set X:=[set x|inner_norm (@euclidean_inner_productP R m) x=r].
pose chi:=@CharacteristicFunction.value R X S.
have hChi:=@CharacteristicFunction.laws R X S.
have hcE:0<=c%:E by rewrite lee_fin.
have hI:=@measure_nonnegative_extended_characteristic_integral R X H
  (@hausdorff_measure_is_measure R X k) S chi c%:E hChi
  (@euclidean_norm_sphere_hausdorff_measurable R m k r) hcE.
apply:measure_integral_graph_equivalent _ hI=>x z.
rewrite partial_function_zero_extension_graph real_total_integrand_graph.
change (c%:E*(chi x)%:E=z <->(S x /\(g x)%:E=z) \/(~S x /\z= 0)).
case:(pselect (S x))=>hx.
- have hOn:chi x = 1%R:=characteristic_on_set hChi hx.
  rewrite hOn mule1 (hg x hx); split=>hz.
  + left; by split.
  + case:hz=>[[_ hz]|[hn _]]=>//; exfalso; exact:hn hx.
- have hOff:chi x = 0%R:=characteristic_off_set hChi hx.
  rewrite hOff mule0; split=>hz.
  + right; split=>//; by symmetry.
  + case:hz=>[[hs _]|[_ hz]]; first by exfalso; exact:hx hs.
    by symmetry.
Qed.
