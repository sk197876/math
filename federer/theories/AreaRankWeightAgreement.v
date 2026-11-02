(** Federer (1969), 3.2.5, p. 245: the auxiliary
    positive-rank cutoff preserves the source weighted integrand
    almost everywhere and the target fibre sum off a null
    image. These consequences use only the cutoff's laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  ExtendedRealOrderTopology LipschitzUP PartialFunctionUP PartialFunctionBasic PartialZeroExtension
  PartialDensityProduct EuclideanJacobianMeasurable PositiveJacobianImageNull BorelAreaSelection
  AreaRankWeightUP AreaTransformIntegrands MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  NonnegativeSum NonnegativeSumSupport NonnegativeSumScale FibreNonnegativeSum MappingMultiplicity CharacteristicFunctionUP CharacteristicFunctionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [area_rank_weight_source_agreement]: the zero
    Jacobian and null-domain reductions in Federer 3.2.5,
    p. 245. On the actual Jacobian domain, every
    excluded nonpositive value is zero. *)
Lemma area_rank_weight_source_agreement (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) A (g:R_n R n->R) u:
  is_metric_lipschitz setT f -> is_area_rank_weight f A g u ->
  measure_almost_equal (@euclidean_lebesgue_measure R m)
    (partial_density_product (partial_function_total u) (extended_euclidean_jacobian f))
    (area_transform_source_integrand f A g).
Proof.
move=>hLip hU; have hm:=euclidean_lebesgue_is_measure R m.
have hJ:=extended_euclidean_jacobian_measurable hLip.
apply:(@measure_almost_everywhere_mono R _ _ hm _ _ _ (measurable_function_domain hJ))=>x [j hj].
exists (u x*j); split.
- apply/partial_density_product_graph; exists (u x),j; by split=>//; split.
- case:(pselect (A x))=>hA.
  + apply:(partial_function_zero_extension_on _ _ _ hA).2.
    apply/partial_density_product_graph; exists (g (f x))%:E,j; split=>//; split=>//.
    case:(pselect (positive_euclidean_jacobian_locus f x))=>hP.
    * by rewrite (area_rank_weight_on hU hA hP).
    * by rewrite (extended_jacobian_zero_outside_positive_locus hP hj) !mule0.
  + apply:(partial_function_zero_extension_off _ _ _ hA).2.
    by rewrite (area_rank_weight_off hU (fun h=>hA h.1)) mul0e.
Qed.

(** Source for [area_rank_weight_fibre_sum]: characteristic
    fibre summation in Federer 3.2.5, p. 245.
    Off the null image discarded by 3.2.3–3.2.4,
    the finite weight is constant on each fibre; zero
    weight and infinite multiplicity are included. *)
Lemma area_rank_weight_fibre_sum (R:realType) m n (f:R_n R m->R_n R n)
    A (g:R_n R n->R) u y:
  is_area_rank_weight f A g u -> (forall z,(0<=g z)%R) ->
  ~((f @` (~` positive_euclidean_jacobian_locus f)) y) ->
  fibre_nonnegative_sum f u y=(g y)%:E*@mapping_multiplicity R _ _ f A y.
Proof.
move=>hU hg hOff.
pose chi:=@CharacteristicFunction.value R (R_n R m) A.
have hChi:is_characteristic_function A chi:=@CharacteristicFunction.laws R (R_n R m) A.
have hPoint x:f x=y -> u x=(g y)%:E*(chi x)%:E.
  move=>hxy.
  have hP:positive_euclidean_jacobian_locus f x.
    apply:contrapT=>hx; apply:hOff; by exists x.
  case:(pselect (A x))=>hA.
  - by rewrite (area_rank_weight_on hU hA hP) hxy (characteristic_on_set hChi hA) mule1.
  - by rewrite (area_rank_weight_off hU (fun h=>hA h.1)) (characteristic_off_set hChi hA) mule0.
have hNonneg x:(0<=chi x)%R.
  case:(pselect (A x))=>hx.
  - rewrite (characteristic_on_set hChi hx); exact:ler01.
  - by rewrite (characteristic_off_set hChi hx).
rewrite /fibre_nonnegative_sum.
transitivity (nonnegative_sum [set x|f x=y] (fun x=>(g y)%:E*(chi x)%:E)).
- apply:nonnegative_sum_ext=>x hx; exact (hPoint x hx).
rewrite nonnegative_sum_scale; last 2 first.
- exact (hg y).
- move=>x _; rewrite lee_fin; exact (hNonneg x).
have hSum:=@fibre_characteristic_sum R [the choiceType of (R_n R m : Type)] (R_n R n) f A chi hChi y.
by rewrite -/(fibre_nonnegative_sum _ _ _) hSum.
Qed.
