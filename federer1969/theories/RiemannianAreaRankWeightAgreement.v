(** Federer (1969), 3.2.5(1), p. 245, extended
    by 3.2.46, p. 282: the independent rank cutoff
    preserves the actual source weighted Jacobian and the
    target fibre sum off the proved null discarded image.
    Only public graph laws and arbitrary counting sums are used. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology
  RiemannianTensorUP RiemannianMetricCarrier RiemannianHausdorff RiemannianPathLipschitz
  RiemannianMapJacobian RiemannianLocalAreaSelection RiemannianAreaJacobianVolumeMeasurable
  RiemannianAreaRankWeightUP RiemannianAreaTransformIntegrands
  PartialFunctionUP PartialFunctionBasic PartialZeroExtension PartialDensityProduct
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  NonnegativeSum NonnegativeSumSupport NonnegativeSumScale FibreNonnegativeSum MappingMultiplicity
  CharacteristicFunctionUP CharacteristicFunctionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [riemannian_jacobian_zero_outside_positive_locus]:
    a defined nonpositive area Jacobian is zero, supporting
    3.2.5(1), p. 245, in 3.2.46, p. 282.
    Undefined differentials are not assigned any value. *)
Lemma riemannian_jacobian_zero_outside_positive_locus (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh) x j :
  ~ positive_riemannian_area_locus f x ->
  partial_function_graph (extended_riemannian_map_jacobian f m) x j -> j=0.
Proof.
move=> hNot [r [hr <-]].
have hNonnegative : (0<=r)%R := riemannian_map_jacobian_nonnegative hr.
have hUpper : (r<=0)%R.
  rewrite leNgt; apply/negP=> hPositive; apply: hNot; exists r; by split.
have hZero : r=0%R by apply/eqP; rewrite eq_le hUpper hNonnegative.
by rewrite hZero.
Qed.

(** Source for [riemannian_area_rank_weight_source_agreement]:
    exact source-product agreement almost everywhere for
    the cutoff in 3.2.5(1), p. 245, supporting
    3.2.46, p. 282. The actual original Jacobian
    has conull domain; its excluded defined values are zero. *)
Lemma riemannian_area_rank_weight_source_agreement (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hp : (0<=m%:R :> R)%R) S u w :
  is_riemannian_path_lipschitz f -> is_riemannian_area_rank_weight f S u w ->
  measure_almost_equal (riemannian_hausdorff_measure hg m%:R hp)
    (partial_density_product (partial_function_total w) (extended_riemannian_map_jacobian f m))
    (riemannian_area_source_integrand f S u).
Proof.
move=> hLip hW.
have hMu := @riemannian_hausdorff_is_measure R m A g hg m%:R hp.
have hJ := @riemannian_area_jacobian_volume_measurable R m n A B g h hg hh f hp hLip.
apply: (@measure_almost_everywhere_mono R _ _ hMu _ _ _ (measurable_function_domain hJ))=> x [j hj].
exists (w x*j); split.
- apply/partial_density_product_graph; exists (w x),j; by split; last split.
- case: (pselect (S x))=> hx.
  + apply: (partial_function_zero_extension_on _ _ _ hx).2.
    apply/partial_density_product_graph; exists (u (f x))%:E,j; split; first by [].
    split; first exact hj.
    case: (pselect (positive_riemannian_area_locus f x))=> hP.
    * by rewrite (riemannian_area_rank_weight_on hW hx hP).
    * by rewrite (riemannian_jacobian_zero_outside_positive_locus hP hj) !mule0.
  + apply: (partial_function_zero_extension_off _ _ _ hx).2.
    by rewrite (riemannian_area_rank_weight_off hW (fun h=>hx h.1)) mul0e.
Qed.

(** Source for [riemannian_area_rank_weight_fibre_sum]:
    constant-on-fibre characteristic summation in 3.2.5(1),
    p. 245, supporting 3.2.46, p. 282. Off
    the discarded nonpositive-rank image the full original
    fibre count remains, including zero weights on infinite fibres. *)
Lemma riemannian_area_rank_weight_fibre_sum (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh) S u w y :
  is_riemannian_area_rank_weight f S u w -> (forall z, (0<=u z)%R) ->
  ~ ((f @` (~`positive_riemannian_area_locus f)) y) ->
  fibre_nonnegative_sum f w y=(u y)%:E*@mapping_multiplicity R _ _ f S y.
Proof.
move=> hW hU hOff.
pose X := [the choiceType of riemannian_metric_space hg].
pose chi := @CharacteristicFunction.value R X S.
have hChi := @CharacteristicFunction.laws R X S.
have hPoint x : f x=y -> w x=(u y)%:E*(chi x)%:E.
  move=> hxy.
  have hP : positive_riemannian_area_locus f x.
    apply: contrapT=> hx; apply: hOff; by exists x.
  case: (pselect (S x))=> hx.
  - by rewrite /chi (riemannian_area_rank_weight_on hW hx hP) hxy (characteristic_on_set hChi hx) mule1.
  - by rewrite /chi (riemannian_area_rank_weight_off hW (fun h=>hx h.1)) (characteristic_off_set hChi hx) mule0.
have hNonnegative x : (0<=chi x)%R.
  case: (pselect (S x))=> hx.
  - rewrite /chi (characteristic_on_set hChi hx); exact: ler01.
  - by rewrite /chi (characteristic_off_set hChi hx).
rewrite /fibre_nonnegative_sum.
transitivity (nonnegative_sum [set x | f x=y] (fun x=>(u y)%:E*(chi x)%:E)).
- apply: nonnegative_sum_ext=> x hx; exact: hPoint x hx.
rewrite nonnegative_sum_scale; last 2 first.
- exact: hU y.
- move=> x _; rewrite lee_fin; exact: hNonnegative x.
have hSum := @fibre_characteristic_sum R X [the choiceType of riemannian_metric_space hh] f S chi hChi y.
by rewrite -/(fibre_nonnegative_sum _ _ _) hSum.
Qed.
