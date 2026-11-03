(** Regression checks for Federer (1969), 3.1.1, pp. 209–210.
    These test the exact domain requirement, the sealed differential graph
    and the zero-dimensional boundary. They are supporting examples, not
    additional assertions attributed to Federer. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP PartialFunctionUP Rectifiability
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm InnerMetric EuclideanLebesgueDimensions TensorFamilyUP NormMetric LinearBasis CompleteMetricUP TopologicalBorel TensorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [constant_differential_graph_regression]: supporting
    constant-map instance of Df in Federer 3.1.1, p. 209. The result uses
    only the public graph law, not its private implementation. *)
Example constant_differential_graph_regression (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY) (a : X) (c : Y) :
  partial_function_graph (norm_differential hNX hNY (fun _ => True)
    (fun _ => c)) a 0.
Proof.
apply: (proj2 (@norm_differential_graph R X Y NX NY hNX hNY
  (fun _ => True) (fun _ => c) a 0)).
apply: (@norm_differential_constant R X Y NX NY hNX hNY (fun _ => True) a c).
exists 1; split; first exact: ltr01.
by move=> h _.
Qed.

(** Source for [empty_domain_not_differentiable_regression]: the
    interior-domain hypothesis in Federer 3.1.1, p. 209, excludes every
    point of the empty domain, even for a constant total representative. *)
Example empty_domain_not_differentiable_regression (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (f : X -> Y) (a : X) :
  ~ norm_differentiable_at NX NY (fun _ => False) f a.
Proof.
move=> [L hf].
exact: (norm_domain_interior_member hNX (norm_differential_interior hf)).
Qed.

(** Source for [halfline_boundary_not_differentiable_regression]: a local
    domain regression for Federer 3.1.1, p. 209. A one-sided boundary
    point is excluded by his interior requirement, irrespective of the
    chosen function or of any one-sided derivative. *)
Example halfline_boundary_not_differentiable_regression (R : realType)
    (f : R -> R) :
  ~ @norm_differentiable_at R R^o R^o (fun t => `|t|) (fun t => `|t|)
      (fun t => 0 <= t) f 0.
Proof.
move=> [L hf]; have [r [hr hA]] := norm_differential_interior hf.
have hhalf : 0 < r/2 by rewrite divr_gt0 // ltr0n.
have hsmall : `|-(r/2)| < r.
  rewrite normrN (ger0_norm (ltW hhalf)); by lra.
have hh := hA (-(r/2)) hsmall; rewrite add0r in hh.
by lra.
Qed.

(** Source for [zero_source_differential_regression]: supporting
    zero-dimensional case of Federer 3.1.1, p. 209. On a source whose
    only vector is zero, every total map has the unique zero differential. *)
Example zero_source_differential_regression (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (hz : forall x : X, x=0) (f : X -> Y) (a : X) :
  has_norm_differential NX NY (fun _ => True) f a 0.
Proof.
have hi : norm_domain_interior NX (fun _ => True) a.
  exists 1; split; first exact: ltr01.
  by move=> h _.
have hc := @norm_differential_constant R X Y NX NY hNX hNY
  (fun _ => True) a (f 0) hi.
apply: (@norm_differential_domain_agreement R X Y NX NY hNX
  (fun _ => True) (fun _ => f 0) f a 0) _ hc.
by move=> x _; rewrite (hz x).
Qed.

(** Source for [constant_sharp_ratios_regression]: the sharp limits
    of Federer 3.1.1, p. 209, are both zero for a constant map on a
    nonzero source. This tests sharpness even when the differential has
    zero minimum modulus, rather than an invertible differential. *)
Example constant_sharp_ratios_regression (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (hX : exists x : X, x != 0) (a : X) (c : Y) :
  is_norm_ratio_limsup NX NY (fun _ => True) (fun _ => c) a 0 /\
  is_norm_ratio_liminf NX NY (fun _ => True) (fun _ => c) a 0.
Proof.
have ha : norm_domain_interior NX (fun _ => True) a.
  exists 1; split; first exact: ltr01.
  by move=> h _.
have hf := @norm_differential_constant R X Y NX NY hNX hNY (fun _ => True) a c ha.
have hn : is_norm_operator_norm NX NY (0 : Hom X Y) 0.
  constructor.
  - exact: lexx.
  - by move=> x; rewrite hom_zeroE (real_seminorm_zero hNY.1) mul0r.
  - by move=> C hC _.
have hm : is_norm_minimum_modulus NX NY (0 : Hom X Y) 0.
  constructor.
  - exact: lexx.
  - by move=> x; rewrite hom_zeroE (real_seminorm_zero hNY.1) mul0r.
  - move=> C hC; have [u hu] := norm_unit_direction_exists hNX hX.
    have hh := hC u; by rewrite hu mulr1 hom_zeroE (real_seminorm_zero hNY.1) in hh.
exact: (norm_differential_sharp_limits hNX hNY hX hf hn hm).
Qed.

(** Source for [zero_source_no_finite_ratios_regression]: the same
    constant-map example has no finite sharp increment-ratio limits when
    its source is zero dimensional. This verifies the qualification of
    Federer 3.1.1, p. 209, against the earlier zero-source differential test. *)
Example zero_source_no_finite_ratios_regression (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (hz : forall x : X, x = 0)
    (a : X) (c : Y) (l : R) :
  ~ is_norm_ratio_limsup NX NY (fun _ => True) (fun _ => c) a l /\
  ~ is_norm_ratio_liminf NX NY (fun _ => True) (fun _ => c) a l.
Proof. exact: (@norm_ratio_zero_source_exception R X Y NX NY hNX
  (fun _ => True) (fun _ => c) a l hz). Qed.


(** Source for [continuous_partials_affine_regression]: supporting
    test of Federer's final criterion in 3.1.1, p. 211. A vector-valued
    affine map has the prescribed differential in every finite source
    dimension, including zero, without completeness of the target.
    The proof supplies coordinate quotients directly to the criterion. *)
Example continuous_partials_affine_regression (R : realType) n
    (Y : lmodType R) (NY : Y -> R) (hNY : is_real_norm NY)
    (L : Hom (R_n R n) Y) (a : R_n R n) (b : Y) :
  has_norm_differential (inner_norm (@euclidean_inner_productP R n)) NY
    (fun _ => True) (fun x => L x+b) a L.
Proof.
apply: (@continuous_partials_differential R n Y NY hNY (fun _ => True)
  (fun x => L x+b) a (fun i _ => L (@coordinate_basis R n i)) L)=> //.
- exists 1; split; first exact: ltr01.
  move=> x _; split=> // i e he.
  exists 1; split; first exact: ltr01.
  move=> t ht; have ht0 : t != 0 by move: (andP ht).1; rewrite normr_gt0.
  have hinc : (L (x+t *: (@coordinate_basis R n i))+b)-(L x+b) =
      t *: L (@coordinate_basis R n i).
    by rewrite [x+t *: (@coordinate_basis R n i)]addrC
      (hom_linear L) -(addrA (t *: L (@coordinate_basis R n i)) (L x) b) addrK.
  rewrite hinc scalerA mulVf // scale1r subrr (real_seminorm_zero hNY.1).
  exact he.
- move=> i e he; exists 1; split; first exact: ltr01.
  by move=> x _ _; rewrite subrr (real_seminorm_zero hNY.1).
Qed.


(** Source for [empty_multilinear_product_regression]: supporting
    empty-product test of Federer 3.1.1(4), p. 210. A zero-linear
    map may have an arbitrary nonzero constant value. Its derivative
    is zero. The product carrier and norm remain opaque throughout. *)
Example empty_multilinear_product_regression (R : realType)
    (Y : lmodType R) (NY : Y -> R) (hNY : is_real_norm NY) (c : Y) :
  let V := fun _ : 'I_0 => R^o in
  let N := fun _ : 'I_0 => fun x : R^o => `|x| in
  let P := @NormedFamily.space R 0 V in
  let PN := @NormedFamily.norm R 0 V N in
  forall a : P, has_norm_differential PN NY (fun _ => True) (fun _ => c) a 0.
Proof.
move=> V N P PN a.
pose coordinate := @NormedFamily.coordinate R 0 V.
have hP : is_normed_family N coordinate PN := @NormedFamily.laws R 0 V N.
have hN : forall i, is_real_norm (N i).
  by move=> i; exact: scalar_absolute_value_norm.
pose f := fun _ : {dffun forall i, V i} => c.
have hf : multilinear f.
  move=> x i; have hi := ltn_ord i; by rewrite ltn0 in hi.
have hc : norm_class_zero PN NY (fun _ => True)
    (fun x => f [ffun i : 'I_0 => coordinate i x]).
  move=> x _; split.
  - exists 1; split; first exact: ltr01.
    by move=> h _.
  - move=> e he; exists 1; split; first exact: ltr01.
    by move=> h _ _; rewrite /f subrr (real_seminorm_zero hNY.1).
have [L [hD hL]] := @norm_differential_multilinear R 0 V Y P N NY hN hNY
  coordinate PN hP f hf hc a.
have hzero : L=0.
  apply: hom_ext=> v; by rewrite hL big_ord0 hom_zeroE.
by rewrite hzero in hD.
Qed.

(** Source for [zero_source_operator_space_regression]: supporting
    zero-dimensional check of the normed operator space in 3.1.1,
    p. 211. Even with an arbitrary target, the sealed operator
    space has only its zero vector and its norm is zero. *)
Example zero_source_operator_space_regression (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (hx : forall x : X, x=0) :
  let Z := @ContinuousOperator.space R X Y NX NY hNX hNY in
  let ZN := @ContinuousOperator.norm R X Y NX NY hNX hNY in
  forall z : Z, z=0 /\ ZN z=0.
Proof.
move=> Z ZN z.
pose ev := @ContinuousOperator.evaluation R X Y NX NY hNX hNY.
have hZ : is_continuous_operator_space NX NY ev ZN :=
  @ContinuousOperator.laws R X Y NX NY hNX hNY.
have hz : z=0.
  apply: (continuous_operator_injective hZ); apply: hom_ext=> x.
  by rewrite (hx x) !linear0.
split=> //; rewrite hz; exact: real_seminorm_zero (continuous_operator_norm_is_norm hNY hZ).1.
Qed.

(** Source for [open_domain_identity_borel_regression]: supporting
    domain check of 3.1.1, p. 211. The identity on an arbitrary
    open subset of a finite-dimensional normed space has exactly
    that differentiability domain, and the new theorem proves its
    domain Borel. The open domain itself need not be complete. *)
Example open_domain_identity_borel_regression (R : realType)
    (X : lmodType R) (NX : X -> R) (hNX : is_real_norm NX)
    n (e : 'I_n -> X) (he : is_basis e) (A : set X) :
  @open [the topologicalType of real_norm_metric_space hNX] A ->
  partial_function_domain (norm_differential hNX hNX A (fun x : X=>x))=A /\
  @borel_set [the topologicalType of real_norm_metric_space hNX]
    (partial_function_domain (norm_differential hNX hNX A (fun x : X=>x))).
Proof.
move=> ho.
pose L := hom_of_linear (linear_id X).
have hL : norm_bounded_linear NX NX L.
  exists 1; split; first exact: ler01.
  by move=> x; rewrite mul1r.
have hD a : A a -> has_norm_differential NX NX A (fun x : X=>x) a L.
  move=> ha; apply: (@norm_differential_linear R X X NX NX hNX hNX A a L _ hL).
  apply: (@norm_domain_interior_neighbourhood R X NX hNX A a).2.
  rewrite openE in ho; exact: ho a ha.
have hc : norm_class_zero NX NX A (fun x : X=>x).
  exact: (@norm_everywhere_differentiable_class_zero R X X NX NX hNX A
    (fun x : X=>x) (fun _=>L) hD).
split.
- apply/seteqP; split=> a.
  + move=> [M hM]; apply: (@norm_domain_interior_member R X NX hNX A a).
    exact: norm_differential_interior ((norm_differential_graph hNX hNX A (fun x : X=>x) a M).1 hM).
  + move=> ha; exists L.
    exact: (norm_differential_graph hNX hNX A (fun x : X=>x) a L).2 (hD a ha).
- pose Z := @ContinuousOperator.space R X X NX NX hNX hNX.
  pose ev := @ContinuousOperator.evaluation R X X NX NX hNX hNX.
  pose ZN := @ContinuousOperator.norm R X X NX NX hNX hNX.
  have hZ : is_continuous_operator_space NX NX ev ZN := @ContinuousOperator.laws R X X NX NX hNX hNX.
  exact: (@norm_differential_domain_borel R X X Z NX NX hNX hNX ev ZN hZ n e he A
    (fun x : X=>x) hc (@finite_norm_metric_complete R X NX hNX n e he)).
Qed.

(** Source for [approximate_affine_punctured_domain_regression]: supporting
    actual-domain example for Federer 3.1.2, p. 212. Removing one point
    from an affine map leaves its approximate differential at every other
    point, and never assigns a differential at the removed point. *)
Example approximate_affine_punctured_domain_regression (R : realType) n
    (Y : lmodType R) (NY : Y -> R) (hNY : is_real_norm NY)
    (L : Hom (R_n R n.+1) Y) (c : Y) (a b : R_n R n.+1) :
  a!=b ->
  partial_function_graph (approximate_differential hNY (fun x=>x!=b)
    (fun x=>L x+c)) a L /\
  ~ partial_function_domain (approximate_differential hNY (fun x=>x!=b)
    (fun x=>L x+c)) b.
Proof.
move=> hab; split.
- apply: (approximate_differential_graph hNY _ _ a L).2.
  apply: (@approximate_differential_affine_conull R n Y NY hNY
    (fun x=>x!=b) (fun x=>L x+c) L c a)=> //.
  have he : ~` [set x : inner_metric_space (@euclidean_inner_productP R n.+1) | x!=b]=[set b].
    apply/seteqP; split=> x.
    + move=> hn; have [hx|hx] := eqVneq x b; first exact hx.
      by exfalso; exact: hn hx.
    + move=> hx; change (x=b) in hx.
      rewrite hx; by move=> /negP; apply.
  rewrite he; exact: positive_euclidean_singleton_null.
- move=> [M hM].
  have hh := (approximate_differential_graph hNY _ _ b M).1 hM.
  by have := hh.1; rewrite eqxx.
Qed.

(** Source for [approximate_zero_source_empty_regression]: dimension-zero
    convention check for the punctured quotient of Federer 3.1.2, p. 212.
    The unit-mass empty product cannot have a density-one empty domain. *)
Example approximate_zero_source_empty_regression (R : realType) (Y : lmodType R)
    (NY : Y -> R) (hNY : is_real_norm NY) (A : R_n R 0 -> Prop)
    (f : R_n R 0 -> Y) a :
  ~ partial_function_domain (approximate_differential hNY A f) a.
Proof.
move=> [L hL]; apply: (@zero_dimensional_no_approximate_differential R Y NY A f a L).
exact: (approximate_differential_graph hNY A f a L).1 hL.
Qed.

(** Source for [approximate_affine_partial_regression]: affine coordinate
    quotient in Federer 3.1.2, p. 212, checked through the sealed public
    partial derivative rather than a selected graph implementation. *)
Example approximate_affine_partial_regression (R : realType) n (Y : lmodType R)
    (NY : Y -> R) (hNY : is_real_norm NY) (L : Hom (R_n R n) Y) (c : Y) a i :
  partial_function_graph (approximate_partial_derivative hNY setT
    (fun x=>L x+c) i) a (L (@coordinate_basis R n i)).
Proof.
apply: (approximate_partial_derivative_graph hNY _ _ i a _).2.
exact: approximate_partial_derivative_affine.
Qed.

From Federer Require Import EuclideanNoncenteredVitali MetricClosedBalls
  PartialFunctionBasic MeasureUP MeasureBasic MeasureSetDensity
  MeasureApproximateOrderLimits ExtendedRealBounds ExtendedRealOrderTopology
  CenteredBallRelations ZeroDensityCover.

(** Source for [empty_section_order_limits_regression]: supporting
    domain boundary of Federer 3.1.3(2), p. 213, with the corrected
    definitions of 2.9.12. An everywhere undefined section has upper
    limit positive infinity and lower limit negative infinity. *)
Example empty_section_order_limits_regression (R : realType) k
    (a : inner_metric_space (@euclidean_inner_productP R k)) :
  let f := @partial_function_empty (inner_metric_space (@euclidean_inner_productP R k))
    (extended_real_line R) in
  let V := @centered_closed_ball_relation R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R k)] in
  measure_approximate_upper_limit (@euclidean_lebesgue_measure R k) V f a=+oo%E /\
  measure_approximate_lower_limit (@euclidean_lebesgue_measure R k) V f a=-oo%E.
Proof.
move=> f V.
have hbad : ~ partial_function_graph (measure_set_density (@euclidean_lebesgue_measure R k) V setT) a 0%E.
  move=> h.
  apply: (@zero_density_cover_impossible R _ _ V setT setT a
    (euclidean_approximate_context R k) _ h h).
  by rewrite setUT.
have he W : partial_function_preimage f W=set0.
  apply/seteqP; split=> x; last by case.
  by move=> [y [hy _]]; exact hy.
have hu : measure_approximate_upper_thresholds (@euclidean_lebesgue_measure R k) V f a=set0.
  apply/seteqP; split=> t; last by case.
  move=> ht; apply: hbad.
  have hh : partial_function_graph (measure_set_density (@euclidean_lebesgue_measure R k) V
    (~` partial_function_preimage f [set y | (y<=t)%E])) a 0%E := ht.
  by rewrite he setC0 in hh.
have hl : measure_approximate_lower_thresholds (@euclidean_lebesgue_measure R k) V f a=set0.
  apply/seteqP; split=> t; last by case.
  move=> ht; apply: hbad.
  have hh : partial_function_graph (measure_set_density (@euclidean_lebesgue_measure R k) V
    (~` partial_function_preimage f [set y | (t<=y)%E])) a 0%E := ht.
  by rewrite he setC0 in hh.
by rewrite /measure_approximate_upper_limit /measure_approximate_lower_limit
  hu hl extended_real_inf_empty extended_real_sup_empty.
Qed.

(** Source for [null_pullback_needs_epimorphism_regression]: supporting
    necessity of the epimorphism hypothesis in the null-set transport
    behind Federer 3.1.3(3)–(4), p. 213. A constant linear map pulls
    the null singleton at zero back to a set of positive measure. *)
Example null_pullback_needs_epimorphism_regression (R : realType) :
  @euclidean_lebesgue_measure R 1 [set (0%R : inner_metric_space (@euclidean_inner_productP R 1))]=0%E /\
  (0<@euclidean_lebesgue_measure R 1
    ((fun _ : inner_metric_space (@euclidean_inner_productP R 1)=>
      (0%R : inner_metric_space (@euclidean_inner_productP R 1))) @^-1`
        [set (0%R : inner_metric_space (@euclidean_inner_productP R 1))]))%E.
Proof.
split; first exact: positive_euclidean_singleton_null.
apply: lt_le_trans (@euclidean_closed_ball_positive R 1
  (0%R : inner_metric_space (@euclidean_inner_productP R 1)) 1 ltr01) _.
apply: (measure_mono (euclidean_lebesgue_is_measure R 1))=> x _; by [].
Qed.

(** Source for [zero_coordinate_slice_translation_regression]: empty
    first-block boundary of the explicit map in Federer 3.1.3(4),
    p. 213. Every zero-dimensional increment leaves the point fixed. *)
Example zero_coordinate_slice_translation_regression (R : realType) l
    (a : inner_metric_space (@euclidean_inner_productP R (0+l))) (z : R_n R 0) :
  @euclidean_slice_translation R 0 l a z=a.
Proof. by rewrite (@coordinate_zero R z) euclidean_slice_translation_zero. Qed.

From Federer Require Import HilbertFormCompactness MeasureApproximateLimitUP ApproximateLimitEmptyDomain
  EuclideanSliceVariationSets EuclideanSliceUniformCutoffs ProductSections.

(** Source for [zero_target_singleton_no_partial_regression]: empty-target
    boundary of the scalar reduction in Federer 3.1.4, p. 214. A singleton
    source contains the base point but has no nonzero coordinate increment;
    the approximate partial is undefined even though target coordinate
    conditions alone are vacuous. *)
Example zero_target_singleton_no_partial_regression (R : realType) m
    (a : R_n R m) (i : 'I_m) :
  ~ partial_function_domain (approximate_partial_derivative
    (inner_norm_real_norm (@euclidean_inner_productP R 0)) [set a]
    (fun _=>0) i) a.
Proof.
move=> [v hv].
have [ha hl] := (approximate_partial_derivative_graph
  (inner_norm_real_norm (@euclidean_inner_productP R 0)) [set a]
  (fun _=>0) i a v).1 hv.
have hd := approximate_limit_domain_density hl.
have hdom : partial_function_domain (approximate_partial_quotient
    (inner_norm_real_norm (@euclidean_inner_productP R 0)) [set a]
    (fun _=>0) a i)=set0.
  apply/seteqP; split=> t; last by [].
  move=> [z [[ht hx] _]].
  change (a+t*:(@coordinate_basis R m i)=a) in hx.
  have hc := congr1 (fun x : R_n R m=>x i) hx.
  rewrite /coordinate_basis !ffunE eqxx in hc.
  change (a i+t*1=a i) in hc.
  rewrite mulr1 in hc.
  have ht0 : t=0 by lra.
  by move: ht; rewrite ht0 eqxx.
rewrite hdom setC0 in hd.
exact: whole_set_density_not_zero (scalar_approximate_context R) hd.
Qed.

(** Source for [slice_variation_weak_threshold_regression]: the
    corrected weak inequality of Federer 3.1.4, erratum p. 4,
    book p. 214 line 24,
    tested at equality. At zero tolerance the zero shift is exceptional;
    replacing the corrected inequality by a strict one would fail here. *)
Example slice_variation_weak_threshold_regression (R : realType) k l
    (B : set (inner_metric_space (@euclidean_inner_productP R (k+l))))
    (g : inner_metric_space (@euclidean_inner_productP R (k+l)) -> R^o) a :
  euclidean_slice_variation_exception B g 0 (a,0).
Proof.
right; by rewrite euclidean_slice_translation_zero subrr normr0.
Qed.


From mathcomp Require Import boolp.
From Federer Require Import EuclideanApproximateDifferentiability
  MeasurableTotalBasic ApproximatePartialDerivativeAffine MeasureAlmostUP MeasureAlmostBasic.

(** Source for [approximate_partial_to_total_constant_regression]:
    the almost-everywhere implication in Federer 3.1.4,
    p. 214, exercised on a constant map with
    full partial-derivative domains. Every target dimension
    is included, so the empty coordinate family must
    still give a differential on the whole positive-dimensional
    source rather than a vacuous relative assertion. *)
Example approximate_partial_to_total_constant_regression (R : realType) m n
    (c : R_n R n) :
  measure_almost_everywhere (@euclidean_lebesgue_measure R m.+1)
    [set a | partial_function_graph
      (approximate_differential
        (inner_norm_real_norm (@euclidean_inner_productP R n)) setT
        (fun _ : R_n R m.+1=>c)) a 0].
Proof.
pose hN := inner_norm_real_norm (@euclidean_inner_productP R n).
pose mu := @euclidean_lebesgue_measure R m.+1.
pose hm := euclidean_lebesgue_is_measure R m.+1.
have hf := @measurable_total_constant R
  [the choiceType of inner_metric_space (@euclidean_inner_productP R m.+1)]
  [the topologicalType of inner_metric_space (@euclidean_inner_productP R n)]
  mu hm c.
have hpa a i : partial_function_graph
    (approximate_partial_derivative hN setT (fun _ : R_n R m.+1=>c) i) a 0.
  have hp := approximate_partial_derivative_affine hN
    (0 : Hom (R_n R m.+1) (R_n R n)) c a i.
  have heq : (fun x : R_n R m.+1=>(0 : Hom (R_n R m.+1) (R_n R n)) x+c)=
      (fun _ : R_n R m.+1=>c).
    apply: funext=>x; by rewrite hom_zeroE add0r.
  rewrite heq hom_zeroE in hp.
  exact: (approximate_partial_derivative_graph hN setT _ i a 0).2 hp.
have hwhole : (\bigcap_i partial_function_domain
    (approximate_partial_derivative hN setT (fun _ : R_n R m.+1=>c) i))=setT.
  apply/seteqP; split=> a // _ i _; by exists 0; exact: hpa.
have [_ [_ ha]] := federer_3_1_4 hf.
rewrite hwhole measure_almost_everywhere_on_whole in ha.
apply: (measure_almost_everywhere_mono hm _ ha).
move=> a [L [v [hL [hv hform]]]].
have hv0 i : v i=0 := partial_function_single_valued (hv i) (hpa a i).
have hL0 : L=0.
  apply: hom_ext=>h; rewrite hform hom_zeroE.
  apply: big1=>i _; by rewrite hv0 scaler0.
by rewrite hL0 in hL.
Qed.

From Federer Require Import ApproximateToOrdinaryDifferential CenteredNullSetDensity
  EuclideanClosedBallVolume EuclideanNoncenteredVitali MeasureBasic.


(** Source for [approximate_to_ordinary_punctured_centers_regression]:
    supporting instance of Federer 3.1.5, p. 216. The set of Lipschitz
    centers omits one point, while the constant map is defined everywhere.
    Its approximate differential becomes its ordinary differential at
    every remaining center, including when the target dimension is zero. *)
Example approximate_to_ordinary_punctured_centers_regression (R : realType) m n
    (a b : R_n R m.+1) (c : R_n R n) :
  a != b ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R m.+1))
    (inner_norm (@euclidean_inner_productP R n)) setT
    (fun _ : R_n R m.+1=>c) a 0.
Proof.
move=> hab.
pose C : set (R_n R m.+1) := ~` [set b].
have hCd : partial_function_graph
    (measure_set_density (@euclidean_lebesgue_measure R m.+1)
      (@centered_closed_ball_relation R
        [the metricType R of inner_metric_space (@euclidean_inner_productP R m.+1)])
      (~` C)) a 0%E.
  rewrite /C setCK.
  apply: (@centered_null_set_density_zero R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R m.+1)]
    (@euclidean_lebesgue_measure R m.+1) [set b] a
    (euclidean_lebesgue_is_measure R m.+1)).
  - move=> x r hr; split; first exact: euclidean_closed_ball_positive.
    by rewrite euclidean_closed_ball_normalized_volume ?ltW // fin_numE.
  - exact: positive_euclidean_singleton_null.
apply: (@federer_3_1_5 R m.+1 n setT C (fun _=>c) 1 1 a 0).
- by move=> x _.
- exact: ltr01.
- exact: ltr01.
- move=> z _ x _; split=> //.
  by rewrite subrr inner_norm0 mul1r inner_norm_nonnegative.
- move=> h; have hab0 : a=b := h.
  by move: hab; rewrite hab0 eqxx.
- exact hCd.
- apply: (@approximate_differential_affine_conull R m (R_n R n) _
    (inner_norm_real_norm (@euclidean_inner_productP R n)) setT
    (fun _=>c) 0 c a).
  + rewrite setCT; exact: (measure_empty (euclidean_lebesgue_is_measure R m.+1)).
  + by move=> x _; rewrite hom_zeroE add0r.
  + exact I.
Qed.

From Federer Require Import Rademacher EuclideanOneCoordinate
  ScalarEuclideanApproximateLimits RealMetricBackground LipschitzUP.

(** Source for [rademacher_absolute_value_regression]: a nonsmooth
    Lipschitz example for Federer 3.1.6, pp. 216–217. The fold of the
    real line satisfies the theorem's premise by the reverse triangle
    inequality; no premise about existence of its partial derivative
    is supplied. *)
Example rademacher_absolute_value_regression (R : realType) :
  measure_almost_everywhere (@euclidean_lebesgue_measure R 1)
    [set a | norm_differentiable_at
      (inner_norm (@euclidean_inner_productP R 1))
      (inner_norm (@euclidean_inner_productP R 1)) setT
      (fun x=>euclidean_one_embed `|euclidean_one_project x|) a].
Proof.
apply: federer_3_1_6.
exists 1; split; first exact: ltr01.
split; first exact: ler01.
move=> x y _ _.
rewrite mul1r euclidean_one_embed_isometry -euclidean_one_project_isometry
  !real_line_metric_distanceE.
exact: ler_dist_dist.
Qed.

(** Source for [rademacher_zero_source_regression]: the zero-dimensional
    source boundary of Federer 3.1.6, pp. 216–217. Every map on the
    singleton source is Lipschitz, so the theorem applies without using
    the impossible punctured approximate-differential premise. *)
Example rademacher_zero_source_regression (R : realType) n
    (f : inner_metric_space (@euclidean_inner_productP R 0)->
      inner_metric_space (@euclidean_inner_productP R n)) :
  measure_almost_everywhere (@euclidean_lebesgue_measure R 0)
    [set a | norm_differentiable_at
      (inner_norm (@euclidean_inner_productP R 0))
      (inner_norm (@euclidean_inner_productP R n)) setT f a].
Proof.
apply: federer_3_1_6.
exists 1; split; first exact: ltr01.
split; first exact: ler01.
by move=> x y _ _; rewrite (coordinate_zero x) (coordinate_zero y) !mdistxx mulr0.
Qed.

(** Source for [rademacher_zero_target_regression]: the empty target
    coordinate family in Federer 3.1.6, pp. 216–217. The result retains
    the ordinary differential on the whole source, even when a finite
    intersection over target coordinates is vacuous. *)
Example rademacher_zero_target_regression (R : realType) m
    (f : inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R 0)) :
  measure_almost_everywhere (@euclidean_lebesgue_measure R m)
    [set a | norm_differentiable_at
      (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R 0)) setT f a].
Proof.
apply: federer_3_1_6.
exists 1; split; first exact: ltr01.
split; first exact: ler01.
by move=> x y _ _; rewrite (coordinate_zero (f x)) (coordinate_zero (f y)) mdistxx mul1r mdist_ge0.
Qed.

From Federer Require Import LipschitzRestrictionDifferentiability.

(** Source for [lipschitz_restriction_zero_target_regression]: the
    zero-target and possibly empty-domain boundary of Federer 3.1.7,
    p. 217. On every measurable subset of a positive-dimensional
    source, almost every domain point has the exact zero approximate
    differential and all zero approximate partials. The empty target
    coordinate family does not discard the actual domain condition. *)
Example lipschitz_restriction_zero_target_regression (R : realType) m
    (A : set (inner_metric_space (@euclidean_inner_productP R m.+1)))
    (f : inner_metric_space (@euclidean_inner_productP R m.+1)->
      inner_metric_space (@euclidean_inner_productP R 0)) :
  measure_measurable (@euclidean_lebesgue_measure R m.+1) A ->
  measure_almost_everywhere_on (@euclidean_lebesgue_measure R m.+1) A
    [set a | partial_function_graph
      (approximate_differential (inner_norm_real_norm (@euclidean_inner_productP R 0)) A f) a 0 /\
      forall i : 'I_m.+1, partial_function_graph
        (approximate_partial_derivative (inner_norm_real_norm (@euclidean_inner_productP R 0)) A f i) a 0].
Proof.
move=> hA.
have hLip : is_metric_lipschitz A f.
  exists 1; split; first exact: ltr01.
  split; first exact: ler01.
  by move=> x y _ _; rewrite (coordinate_zero (f x)) (coordinate_zero (f y)) mdistxx mul1r mdist_ge0.
have hh := federer_3_1_7 hA hLip.
apply: (measure_almost_everywhere_on_implication _ _ _).2.
apply: (measure_almost_everywhere_mono (euclidean_lebesgue_is_measure R m.+1)
  _ ((measure_almost_everywhere_on_implication _ _ _).1 hh)).
move=> a ha hAa; have [L [hL hp]] := ha hAa.
have hzero : L=0.
  apply: hom_ext=> h; rewrite hom_zeroE; exact: coordinate_zero.
rewrite hzero in hL hp.
by split=> // i.
Qed.

(** Supporting regressions for Federer 3.1.8, pp. 217–218. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  InnerMetric EuclideanLebesgueDimensions EuclideanApproximateContext
  EuclideanClosedBallVolume EuclideanNoncenteredVitali ApproximateDifferentialAffine
  CenteredNullSetDensity CenteredBallRelations PartialFunctionUP MeasureSetDensity
  ApproximateOrderThresholdRays MeasureApproximateOrderLimits ApproximateMetricGrowth
  ApproximateGrowthZeroSource ApproximateGrowthDifferentiability ApproximateDifferentialUP
  MeasureAlmostUP LipschitzUP MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [constant_finite_approximate_growth_regression]:
    supporting nonempty-domain instance of the hypothesis in Federer
    3.1.8, p. 217. The constant map has a zero growth quotient on
    its actual punctured domain, whose missing singleton is null in
    positive source dimension. Every target dimension is included. *)
Example constant_finite_approximate_growth_regression (R : realType) m n
    (c : inner_metric_space (@euclidean_inner_productP R n))
    (a : inner_metric_space (@euclidean_inner_productP R m.+1)) :
  (measure_approximate_upper_limit (@euclidean_lebesgue_measure R m.+1)
    (@centered_closed_ball_relation R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R m.+1)])
    (partial_metric_growth_quotient setT (fun _=>c) a) a < +oo)%E.
Proof.
pose X := inner_metric_space (@euclidean_inner_productP R m.+1).
pose F := partial_metric_growth_quotient setT (fun _ : X=>c) a.
apply: (approximate_upper_limit_rational_ray (euclidean_approximate_context R m.+1) F a +oo%E).2.
exists (0 : rat); split; first by rewrite rmorph0 ltry.
have he : partial_function_preimage F [set y | (y<=(0 : R)%:E)%E]=~` [set a].
  apply/seteqP; split=> x.
  - move=> [y [[[hx hn] hy] hqy]] hxa.
    have hEq : x=a := hxa.
    by move: hn; rewrite hEq eqxx.
  - move=> hxa.
    have hne : x!=a by apply/eqP.
    exists 0%E; split.
    + split; first by split.
      change (((mdist c c / mdist x a)%R)%:E = 0%E).
      by rewrite mdistxx mul0r.
    + exact: lexx.
change (partial_function_graph
  (measure_set_density (@euclidean_lebesgue_measure R m.+1)
    (@centered_closed_ball_relation R [the metricType R of X])
    (~` partial_function_preimage F [set y | (y<=(ratr (0 : rat) : R)%:E)%E])) a 0%E).
rewrite rmorph0 he setCK.
apply: (@centered_null_set_density_zero R [the metricType R of X]
  (@euclidean_lebesgue_measure R m.+1) [set a] a (euclidean_lebesgue_is_measure R m.+1)).
- move=> x r hr; split; first exact: euclidean_closed_ball_positive.
  by rewrite euclidean_closed_ball_normalized_volume ?ltW // fin_numE.
- exact: positive_euclidean_singleton_null.
Qed.

(** Source for [finite_growth_constant_differentiability_regression]:
    exercise the final conclusion of Federer 3.1.8, pp. 217–218,
    using the actual finite growth hypothesis just proved, with arbitrary
    finite target dimension including zero. *)
Example finite_growth_constant_differentiability_regression (R : realType) m n
    (c : inner_metric_space (@euclidean_inner_productP R n)) :
  measure_almost_everywhere_on (@euclidean_lebesgue_measure R m.+1) setT
    [set a | approximately_differentiable_at
      (inner_norm (@euclidean_inner_productP R n)) setT (fun _=>c) a].
Proof.
have hg a (_ : @setT (inner_metric_space (@euclidean_inner_productP R m.+1)) a) :=
  @constant_finite_approximate_growth_regression R m n c a.
have [F [hF [hcover ha]]] := federer_3_1_8 hg.
exact ha.
Qed.

(** Source for [zero_source_growth_nonempty_impossible_regression]:
    the singleton-source boundary of Federer 3.1.8, pp. 217–218.
    Its punctured growth hypothesis cannot hold on the whole source,
    including for a zero-dimensional target. *)
Example zero_source_growth_nonempty_impossible_regression (R : realType) n
    (f : inner_metric_space (@euclidean_inner_productP R 0)->
      inner_metric_space (@euclidean_inner_productP R n)) :
  ~ (forall a, (measure_approximate_upper_limit (@euclidean_lebesgue_measure R 0)
    (@centered_closed_ball_relation R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R 0)])
    (partial_metric_growth_quotient setT f a) a < +oo)%E).
Proof.
move=> hg.
have h0 := zero_source_finite_approximate_growth_domain_empty (fun a _=>hg a).
have htrue : @setT (inner_metric_space (@euclidean_inner_productP R 0)) 0 := I.
by rewrite h0 in htrue.
Qed.

(** Source for [zero_source_empty_growth_decomposition_regression]:
    the empty-domain, zero-source case of Federer 3.1.8, pp. 217–218.
    The public theorem supplies a measurable Lipschitz cover, including
    for an arbitrary map into a zero-dimensional target. *)
Example zero_source_empty_growth_decomposition_regression (R : realType) n
    (f : inner_metric_space (@euclidean_inner_productP R 0)->
      inner_metric_space (@euclidean_inner_productP R n)) :
  exists F : (nat*nat)->set (inner_metric_space (@euclidean_inner_productP R 0)),
    (forall q, measure_measurable (@euclidean_lebesgue_measure R 0) (F q) /\
      F q `<=` set0 /\ is_metric_lipschitz (F q) f) /\
    set0=\bigcup_q F q.
Proof.
have hg a : (@set0 (inner_metric_space (@euclidean_inner_productP R 0))) a ->
    (measure_approximate_upper_limit (@euclidean_lebesgue_measure R 0)
      (@centered_closed_ball_relation R
        [the metricType R of inner_metric_space (@euclidean_inner_productP R 0)])
      (partial_metric_growth_quotient set0 f a) a < +oo)%E by case.
have [F [hF [hc _]]] := federer_3_1_8 hg.
by exists F.
Qed.

(** Regression instances of Federer 3.1.9, p. 218. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerMetric EuclideanLebesgueDimensions LocalSlopeBound MetricSlopeLimsup
  LipschitzUP NormDifferentialUP MeasureAlmostUP Stepanoff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [stepanoff_constant_arbitrary_subset_regression]:
    Federer 3.1.9, p. 218, with a constant map on an arbitrary open B.
    No measurability of A is assumed. Both zero-dimensional boundaries
    and the empty domain are included. *)
Example stepanoff_constant_arbitrary_subset_regression (R : realType) m n
    (A B : set (inner_metric_space (@euclidean_inner_productP R m)))
    (c : inner_metric_space (@euclidean_inner_productP R n)) :
  A `<=` B -> open B ->
  measure_almost_everywhere_on (@euclidean_lebesgue_measure R m) A
    [set a | norm_differentiable_at
      (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n)) B (fun _=>c) a].
Proof.
move=> hAB hB; apply: (federer_3_1_9 hAB hB)=> a ha.
have hbound : is_metric_lipschitz_bound B (fun _=>c) (0 : R).
  split; first exact: lexx.
  by move=> x y _ _; rewrite mdistxx mul0r.
have hs := metric_slope_local_bound_implies_limsup
  (metric_bound_is_local_slope_bound hbound) (hAB a ha).
apply: le_lt_trans hs _.
by rewrite ltry.
Qed.

(** Source for [stepanoff_zero_target_regression]: the empty target
    coordinate family in Federer 3.1.9, p. 218. Every map into R^0
    satisfies the actual finite limsup hypothesis on its open domain. *)
Example stepanoff_zero_target_regression (R : realType) m
    (A B : set (inner_metric_space (@euclidean_inner_productP R m)))
    (f : inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R 0)) :
  A `<=` B -> open B ->
  measure_almost_everywhere_on (@euclidean_lebesgue_measure R m) A
    [set a | norm_differentiable_at
      (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R 0)) B f a].
Proof.
move=> hAB hB; apply: (federer_3_1_9 hAB hB)=> a ha.
have hbound : is_metric_lipschitz_bound B f (0 : R).
  split; first exact: lexx.
  by move=> x y _ _; rewrite (coordinate_zero (f x)) (coordinate_zero (f y)) mdistxx mul0r.
have hs := metric_slope_local_bound_implies_limsup
  (metric_bound_is_local_slope_bound hbound) (hAB a ha).
apply: le_lt_trans hs _.
by rewrite ltry.
Qed.

(** Focused regression examples for Federer 3.1.11. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import Hom RealNormUP PartialFunctionUP NormDifferentialUP
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearZero
  NormHigherDifferentialUP NormHigherDifferential NormHigherDifferentialUnique
  NormHigherDifferentialConstant NormIteratedDirectionalUP NormIteratedPartial
  ScalarReciprocalHigherDifferentials FlatExponentialSealed FlatExponentialSmooth
  ScalarUnitCutoffUP ScalarUnitCutoffSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [higher_zero_order_nonzero_regression]: a
    nonzero constant has a nonzero zeroth differential even
    on the zero-dimensional source; positive orders vanish.
    This checks the empty-product convention of Federer
    3.1.11, pp. 218–221, through the sealed graph. *)
Example higher_zero_order_nonzero_regression (R : realType) (c : R) : c!=0 ->
  let NX := inner_norm (@euclidean_inner_productP R 0) in
  let hNX := inner_norm_real_norm (@euclidean_inner_productP R 0) in
  let NY := fun t : R^o=>`|t| in
  let hNY := @scalar_absolute_value_norm R in
  let Z k := @ContinuousMultilinear.space R k (R_n R 0) R^o NX NY hNX hNY in
  let ev k := @ContinuousMultilinear.evaluation R k (R_n R 0) R^o NX NY hNX hNY in
  let ZN k := @ContinuousMultilinear.norm R k (R_n R 0) R^o NX NY hNX hNY in
  let hZ k := @ContinuousMultilinear.laws R k (R_n R 0) R^o NX NY hNX hNY in
  exists z : Z 0%N, z!=0 /\
    partial_function_graph (norm_higher_differential hNX hNY hZ (fun _=>True)
      (fun _=>c) 0%N) 0 z /\
    forall k, partial_function_graph (norm_higher_differential hNX hNY hZ
      (fun _=>True) (fun _=>c) k.+1) 0 (0 : Z k.+1).
Proof.
move=>hc NX hNX NY hNY Z ev ZN hZ.
have [z hz] := continuous_multilinear_zero_surjective hNY (@hZ 0%N) c.
exists z; split.
- apply/eqP=>he; move:hz; rewrite he linear0=>h; move:hc; by rewrite -h eqxx.
- split.
  + apply: (@norm_higher_differential_graph R (R_n R 0) R^o NX NY hNX hNY
      Z ev ZN hZ (fun _=>True) (fun _=>c) 0%N 0 z).2; by split.
  + move=>k; apply: (@norm_higher_differential_graph R (R_n R 0) R^o NX NY hNX hNY
      Z ev ZN hZ (fun _=>True) (fun _=>c) k.+1 0 0).2.
    have hopen x (_ : True) : norm_domain_interior NX (fun _=>True) x.
      exists 1; split; first exact: ltr01; by move=>h _.
    exact (@norm_higher_differential_constant R (R_n R 0) R^o NX NY hNX hNY
      Z ev ZN hZ (fun _=>True) hopen c z hz k.+1 0 I).
Qed.

(** Source for [iterated_partial_empty_sequence_regression]:
    the empty ordered sequence is the original partial function,
    even on a nonopen domain, Federer 3.1.11, p. 223. *)
Example iterated_partial_empty_sequence_regression (R : realType) n
    (Y : lmodType R) (NY : Y->R) (hNY : is_real_norm NY)
    (A : R_n R n->Prop) (f : R_n R n->Y) a y :
  partial_function_graph (norm_iterated_partial hNY A f [::]) a y <->
    A a /\ y=f a.
Proof. exact (@norm_iterated_partial_graph R n Y NY hNY A f [::] a y). Qed.

(** Source for [reciprocal_second_differential_regression]: the
    second scalar differential is 2/a^3 on the unit arguments,
    for both signs of a. This checks sign, factorial and actual
    domain in Federer 3.1.11, p. 223. *)
Example reciprocal_second_differential_regression (R : realType)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->R^o}->Hom (Z i) R^o) (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space
      (fun t : R^o=>`|t|) (fun t : R^o=>`|t|) (@ev i) (@ZN i)) (a : R) :
  a!=0 -> exists z : Z 2%N,
    has_norm_higher_differential (fun t : R^o=>`|t|) ev ZN
      (fun t=>t!=0) (fun t=>t^-1) 2%N a z /\
    @ev 2%N [ffun _=>1] z= 2*(a^-1)^+3.
Proof.
move=>ha; have [z [hz he]] := @scalar_reciprocal_higher_differentials R Z ev ZN hZ 2%N a ha.
exists z; split; first exact hz.
rewrite he /scalar_reciprocal_derivative_coefficient.
have hp : (\prod_(i<2) [ffun _ : 'I_2=>(1:R)] i)= 1.
  apply: big1=>i _; by rewrite ffunE.
rewrite hp mul1r expr2 mulN1r opprK.
by rewrite !factS fact0 /= !mul1r.
Qed.

(** Source for [flat_exponential_origin_graph_regression]: every
    derivative at the gluing point is zero, including degree zero,
    Federer 3.1.11, p. 223. The exact differential and
    the flat exponential are both used through their sealed laws. *)
Example flat_exponential_origin_graph_regression (R : realType)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->R^o}->Hom (Z i) R^o) (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space
      (fun t : R^o=>`|t|) (fun t : R^o=>`|t|) (@ev i) (@ZN i)) k :
  partial_function_graph (norm_higher_differential (@scalar_absolute_value_norm R)
    (@scalar_absolute_value_norm R) hZ (fun _=>True) (@FlatExponential.value R) k) 0 (0 : Z k).
Proof.
apply: (@norm_higher_differential_graph R R^o R^o _ _
  (@scalar_absolute_value_norm R) (@scalar_absolute_value_norm R)
  Z ev ZN hZ (fun _=>True) (@FlatExponential.value R) k 0 0).2.
exact (flat_exponential_higher_differential_zero hZ k (lexx 0)).
Qed.

(** Regression for the dimension-zero boundary of Federer 3.1.12. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets cardinality reals topology.
From Federer Require Import EuclideanInnerProduct InnerMetric RealMetricBackground
  LipschitzUP LipschitzConstant LipschitzRadiusOverlap LipschitzRadiusDisjointFamily
  MetricClosedBalls CountablyClosedFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lipschitz_radius_zero_dimension_regression]:
    the cardinal bound is one when m=0, the empty-power
    case of Federer 3.1.12, pp. 223–224. The family
    and domain can be empty; finiteness remains a conclusion. *)
Example lipschitz_radius_zero_dimension_regression (R : realType)
    (U S : set (inner_metric_space (@euclidean_inner_productP R 0)))
    (h : inner_metric_space (@euclidean_inner_productP R 0)->R)
    (h_lipschitz : is_metric_lipschitz U (fun y=>(h y : real_line_metric R)))
    (lambda alpha beta : R) x :
  S `<=` U -> (forall y, U y -> 0<h y) ->
  metric_lipschitz_constant h_lipschitz<=lambda ->
  0<alpha -> 0<beta -> lambda*alpha<1 -> lambda*beta<1 ->
  set_family_disjoint [set T | exists s, S s /\ T=metric_closed_ball s (h s)] ->
  U x ->
  finite_set (lipschitz_radius_overlap S h alpha beta x) /\
    ((#|` fset_set (lipschitz_radius_overlap S h alpha beta x)|)%:R : R)<=1.
Proof.
move=>hSU hp hLambda ha hb hla hlb hfamily hx.
have [_ [hfin hbound]] := @federer_3_1_12 R 0 U S h h_lipschitz
  lambda alpha beta x hSU hp hLambda ha hb hla hlb hfamily hx.
split; first exact hfin.
by rewrite !expr0 !mul1r invr1 in hbound.
Qed.

(** Regressions for the boundary cases of Federer 3.1.13. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets cardinality reals topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  ContinuousMultilinearUP TruncatedComplementDistanceUP TruncatedComplementDistanceSealed
  TruncatedComplementDistanceLaws OpenCoverClearanceUP OpenCoverClearanceSealed
  OpenCoverClearanceLaws FedererCoverRadius EuclideanPartitionBallCoverUP
  EuclideanPartitionFamilyUP EuclideanSmoothPartition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [smooth_partition_empty_family_regression]:
    the construction of Federer 3.1.13, pp. 224–225, applied
    to the empty family of open sets selects no centers, since
    S lies in the empty union. *)
Example smooth_partition_empty_family_regression (R : realType) (m : nat)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->R_n R m}->Hom (Z i) R^o)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space
      (inner_norm (@euclidean_inner_productP R m)) (fun t : R^o=>`|t|) (@ev i) (@ZN i)) :
  exists S : set (inner_metric_space (@euclidean_inner_productP R m)),
    is_federer_partition_ball_cover set0 S /\ S=set0.
Proof.
have [Dmu [G [V [_ [_ [_ hPhi]]]]]] := federer_smooth_partition_exists hZ.
have [S [sigma [v [hS _]]]] := hPhi set0 (fun T hT=>match hT with end).
exists S; split; first exact hS.
apply/seteqP; split=>// s hs; have [T hT _] := partition_ball_centers_in_domain hS hs.
exact hT.
Qed.

(** Source for [federer_cover_radius_whole_space_regression]:
    the printed normalisation lambda=1/20 in Federer 3.1.13,
    p. 224: for the family consisting of the whole space the
    capped complement distance is one, so h is constantly 1/20. *)
Example federer_cover_radius_whole_space_regression (R : realType) (X : metricType R) (x : X) :
  federer_cover_radius [set (setT : set X)] x= 1/20.
Proof.
have hlaws := OpenCoverClearance.laws [set (setT : set X)].
have hone : OpenCoverClearance.value [set (setT : set X)] x= 1.
  apply/eqP; rewrite eq_le; apply/andP; split; first exact: (open_cover_clearance_cap hlaws x).
  have hwhole := truncated_complement_distance_whole (TruncatedComplementDistance.laws (@setT X)) x.
  rewrite -hwhole; exact: (open_cover_clearance_upper hlaws x (erefl _)).
by rewrite /federer_cover_radius hone.
Qed.

(** Regressions for the boundary cases of Federer 3.1.14. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology
  constructive_ereal.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness RealNormUP PolynomialFunctions PolynomialRepresentations PolynomialTaylor
  ContinuousMultilinearUP NormHigherDifferentialUP NormClassHigherUP NormHigherSymmetricFormUP
  ExtendedSupremumUP WhitneyModulusUP WhitneyExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [whitney_modulus_empty_regression]:
    rho(C,delta)=0 for the empty set C, since no pair a,b in C
    with 0<|a-b| exists and zero is adjoined, Federer 3.1.14, p. 225. *)
Example whitney_modulus_empty_regression (R : realType) (m : nat) (Y : lmodType R) (NY : Y->R)
    (k : nat) (P : inner_metric_space (@euclidean_inner_productP R m)->PolynomialFunction (R_n R m) Y)
    (delta : R) :
  whitney_modulus NY k P set0 delta=0.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split; last exact: whitney_modulus_nonnegative.
apply: (extended_supremum_least (whitney_modulusP NY k P set0 delta)).
by move=>r [[i [a [b [q [_ [ha _]]]]]]|->] //; case: ha.
Qed.

(** Source for [whitney_modulus_singleton_regression]:
    rho({c},delta)=0, since the single point gives no pair with
    0<|a-b|, Federer 3.1.14, p. 225. *)
Example whitney_modulus_singleton_regression (R : realType) (m : nat) (Y : lmodType R) (NY : Y->R)
    (k : nat) (P : inner_metric_space (@euclidean_inner_productP R m)->PolynomialFunction (R_n R m) Y)
    (c : inner_metric_space (@euclidean_inner_productP R m)) (delta : R) :
  whitney_modulus NY k P [set c] delta=0.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split; last exact: whitney_modulus_nonnegative.
apply: (extended_supremum_least (whitney_modulusP NY k P [set c] delta)).
move=>r [[i [a [b [q [_ [ha [hb [hpos _]]]]]]]]|->] //.
rewrite /= in ha hb; rewrite ha hb subrr in hpos.
by rewrite (real_seminorm_zero (inner_norm_real_norm (@euclidean_inner_productP R m)).1) ltxx in hpos.
Qed.

(** Source for [whitney_extension_empty_regression]:
    the hypotheses of Federer 3.1.14, p. 225, hold for the empty
    closed set with any family of polynomials, and the theorem
    supplies a map of class k on R^m. *)
Example whitney_extension_empty_regression (R : realType) (m : nat) (Y : lmodType R) (NY : Y->R)
    (hNY : is_real_norm NY) (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->R_n R m}->Hom (Z i) Y) (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space
      (inner_norm (@euclidean_inner_productP R m)) NY (@ev i) (@ZN i))
    (k : nat) (P : inner_metric_space (@euclidean_inner_productP R m)->PolynomialFunction (R_n R m) Y) :
  is_whitney_jet_family NY k P set0 /\
  exists g : inner_metric_space (@euclidean_inner_productP R m)->Y,
    norm_class_higher (inner_norm (@euclidean_inner_productP R m)) NY ev ZN (fun _=>True) g k.
Proof.
have hjet : is_whitney_jet_family NY k P set0.
  split; first exact: closed0.
  split; first by move=>a [].
  move=>C hC _ e he; exists 1; split; first exact: ltr01.
  move=>d _ _.
  have hC0 : C=set0 by apply/seteqP; split=>[x hx|x []]; exact: (hC x hx).
  by rewrite hC0 whitney_modulus_empty_regression lee_fin; exact: ltW he.
split; first exact hjet.
have [g [hg _]] := federer_3_1_14 hNY hZ hjet.
by exists g.
Qed.

(** Regressions for the boundary cases of Federer 3.1.15. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology
  constructive_ereal.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness RealNormUP ContinuousMultilinearUP ContinuousMultilinearNorm NormHigherDifferentialUP
  NormHigherDifferentialUnique NormClassHigherUP NormHigherDifferentialConstant
  EuclideanLebesgueDimensions WhitneyFormBridge LusinClassApproximation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lusin_approximation_zero_dimension_regression]:
    in dimension zero the growth hypothesis of Federer 3.1.15,
    p. 227, holds for every map, since the source space is a
    single point, and the theorem supplies a map of class k+1
    agreeing with f up to measure less than epsilon. *)
Example lusin_approximation_zero_dimension_regression (R : realType) (n : nat)
    (Z : nat->lmodType R) (ev : forall i, {ffun 'I_i->R_n R 0}->Hom (Z i) (R_n R n))
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space (inner_norm (@euclidean_inner_productP R 0))
      (inner_norm (@euclidean_inner_productP R n)) (@ev i) (@ZN i))
    (k : nat) (A B : set (inner_metric_space (@euclidean_inner_productP R 0)))
    (f : inner_metric_space (@euclidean_inner_productP R 0)->R_n R n) :
  norm_class_higher (inner_norm (@euclidean_inner_productP R 0))
    (inner_norm (@euclidean_inner_productP R n)) ev ZN B f k ->
  A `<=` B -> forall e : R, 0<e ->
  exists g : inner_metric_space (@euclidean_inner_productP R 0)->R_n R n,
    norm_class_higher (inner_norm (@euclidean_inner_productP R 0))
      (inner_norm (@euclidean_inner_productP R n)) ev ZN (fun _=>True) g k.+1 /\
    (@euclidean_lebesgue_measure R 0 (A `\` [set x | f x=g x])<e%:E)%E.
Proof.
move=>hf hAB e he.
apply: (federer_3_1_15 hZ hf hAB _ he)=>a _ z hz.
exists 0, 1; split; first exact: ltr01.
move=>x w _ hw _.
have hxa : x=a by rewrite (zero_dimension_point x) (zero_dimension_point a).
rewrite hxa in hw.
rewrite (norm_higher_differential_unique (inner_norm_real_norm (@euclidean_inner_productP R 0))
  (inner_norm_real_norm (@euclidean_inner_productP R n)) hZ hw hz) subrr mul0r.
rewrite (real_seminorm_zero (continuous_multilinear_norm_is_norm
  (inner_norm_real_norm (@euclidean_inner_productP R n)) (@hZ k)).1); exact: lexx.
Qed.

(** Source for [lusin_approximation_constant_regression]:
    a constant map is of class 0 on R^m with constant zeroth
    differential, so the hypothesis of Federer 3.1.15, p. 227,
    holds with k=0 and A=B=R^m, and the theorem supplies a map
    of class 1 agreeing with the constant up to measure less
    than epsilon. *)
Example lusin_approximation_constant_regression (R : realType) (m n : nat)
    (Z : nat->lmodType R) (ev : forall i, {ffun 'I_i->R_n R m}->Hom (Z i) (R_n R n))
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n)) (@ev i) (@ZN i))
    (c : R_n R n) (e : R) : 0<e ->
  exists g : inner_metric_space (@euclidean_inner_productP R m)->R_n R n,
    norm_class_higher (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n)) ev ZN (fun _=>True) g 1 /\
    (@euclidean_lebesgue_measure R m ([set: inner_metric_space (@euclidean_inner_productP R m)]
      `\` [set x | c=g x])<e%:E)%E.
Proof.
move=>he.
pose hN := inner_norm_real_norm (@euclidean_inner_productP R m).
pose hNY := inner_norm_real_norm (@euclidean_inner_productP R n).
have hf : norm_class_higher (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) ev ZN (fun _=>True) (fun _=>c) 0%N.
  exact: (norm_class_infinity_constant hN hNY hZ (@whitney_whole_space_interior R m) c 0%N).
apply: (federer_3_1_15 hZ hf (fun x _=>I) _ he)=>a _ z hz.
exists 0, 1; split; first exact: ltr01.
move=>x w _ hw _.
have hzx : has_norm_higher_differential (inner_norm (@euclidean_inner_productP R m)) ev ZN
    (fun _=>True) (fun _=>c) 0%N x z := hz.
rewrite (norm_higher_differential_unique hN hNY hZ hw hzx) subrr mul0r.
rewrite (real_seminorm_zero (continuous_multilinear_norm_is_norm hNY (@hZ 0%N)).1); exact: lexx.
Qed.

(** Regression for Federer 3.1.16, p. 228: the empty actual domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  ContinuousMultilinearUP NormClassHigherUP EuclideanLebesgueDimensions
  MeasureAlmostUP MeasureBasic ApproximateGrowthClassOneApproximation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [class_one_approximation_empty_domain_regression]: the
    empty-domain boundary of Federer 3.1.16, p. 228. No regularity of
    the arbitrary total representative f is required. Every finite source
    and target dimension, including zero, is covered. *)
Example class_one_approximation_empty_domain_regression (R : realType) (m n : nat)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->R_n R m}->Hom (Z i) (R_n R n))
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space
      (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n)) (@ev i) (@ZN i))
    (f : inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) (e : R) :
  0<e -> exists g,
    norm_class_higher (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n)) ev ZN (fun _=>True) g 1%N /\
    (@euclidean_lebesgue_measure R m (set0 `\` [set x | f x=g x])<e%:E)%E.
Proof.
move=>he.
apply: (@federer_3_1_16 R m n Z ev ZN hZ set0 f _ e he).
rewrite /measure_almost_everywhere_on set0D.
exact: measure_empty (euclidean_lebesgue_is_measure R m).
Qed.

(** Regression for the actual-domain convention in Federer 3.1.17. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  ContinuousMultilinearUP EuclideanLebesgueDimensions MeasureUP MeasureAlmostUP
  ClassOneApproximationUP ClassOneApproximationConverse ClassOneApproximationCounterexamples
  ApproximateGrowthDomainMeasurable.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [zero_target_approximate_growth_measurability_regression]:
    the domain qualification for the converse in Federer 3.1.17, p. 229,
    remains necessary even when the target is zero-dimensional. On a
    positive-dimensional source the zero map has finite approximate growth
    almost everywhere on A exactly when A is measurable. *)
Example zero_target_approximate_growth_measurability_regression (R : realType) m
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->R_n R m.+1}->Hom (Z i) (R_n R 0))
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space
      (inner_norm (@euclidean_inner_productP R m.+1))
      (inner_norm (@euclidean_inner_productP R 0)) (@ev i) (@ZN i))
    (A : set (inner_metric_space (@euclidean_inner_productP R m.+1))) :
  measure_almost_everywhere_on (@euclidean_lebesgue_measure R m.+1) A
    (finite_approximate_growth_points A (fun _=>(0 : inner_metric_space (@euclidean_inner_productP R 0)))) <->
  measure_measurable (@euclidean_lebesgue_measure R m.+1) A.
Proof.
split; first exact: approximate_growth_ae_domain_measurable.
move=>hA.
exact (@class_one_approximation_finite_approximate_growth R m 0 Z ev ZN hZ A (fun _=>0) hA
  (@constant_has_class_one_lusin_approximation R m.+1 0 Z ev ZN hZ A 0)).
Qed.

(** Regression cases for Federer (1969), 3.1.18, pp. 229–230:
    positive rank with a nontrivial fibre, and constant maps in all
    dimensions including zero. Use only public chart specifications. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness FiniteCoordinates NormDifferentialUP
  NormRegularity NormRegularityOperations NormOpenDomainLaws NormClassOneUP
  NormClassOneLinear NormFiniteLinearBound LinearRankUP LinearRankAtLeast
  LinearSurjectiveRank NormRankZero EuclideanBlockLinearMaps ConstantRankChartUP
  ConstantRankTheorem ConstantRankSmooth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [smooth_projection_constant_rank_regression]: regression
    for Federer 3.1.18, pp. 229–230, at rank one with one-dimensional
    complementary fibres. One fixed chart satisfies every finite class. *)
Lemma smooth_projection_constant_rank_regression (R:realType) (a:R_n R (1+1)) :
  exists (U:set (R_n R (1+1))) (e:R)
    (p:{linear R_n R 1->R_n R 1}) (j:{linear R_n R 1->R_n R 1})
    (g G:R_n R (1+1)->R_n R (1+1)) (psi:R_n R 1->R_n R 1), forall k,
  @is_euclidean_constant_rank_chart R 1 1 1 k setT
    (@euclidean_first_block_map R 1 1) (fun _=>@euclidean_first_block_map R 1 1)
    a U e p j g G psi.
Proof.
pose X:=R_n R (1+1).
pose Y:=R_n R 1.
pose NX:=inner_norm (@euclidean_inner_productP R (1+1)).
pose NY:=inner_norm (@euclidean_inner_productP R 1).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R (1+1)).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R 1).
pose f:=@euclidean_first_block_map R 1 1.
have hbound:=@norm_finite_linear_bounded R X Y NX NY hNX hNY (1+1)
  (@coordinate_basis R (1+1)) (@coordinate_basisP R (1+1)) f.
have hopen x (hx:setT x):norm_domain_interior NX setT x:=@norm_full_domain_interior R X NX x.
have hf:norm_class_all_orders hNX hNY setT f.
  move=>k; exact (@norm_class_linear R X Y NX NY hNX hNY setT f k hopen hbound).
have hD:=@norm_class_one_linear_field R X Y NX NY hNX hNY setT f hopen hbound.
have hs y:exists x:X, f x=y.
  exists (@euclidean_first_injection_map R 1 1 y).
  exact (@euclidean_first_block_injectionK R 1 1 y).
have ht:=@linear_surjective_rank_at_least R X Y 1 (@coordinate_basis R 1)
  (@coordinate_basisP R 1) f hs.
have hrank:=@linear_rank_from_full_threshold R X Y 1 (@coordinate_basis R 1)
  (@coordinate_basisP R 1) f ht.
have hgen:norm_generic_rank NX setT (fun _=>f) a 1%N.
  exists 1; split; first exact: ltr01.
  by move=>h hh; split.
exact (@federer_3_1_18_smooth R 1 1 1 setT f (fun _=>f) a hf hD hgen).
Qed.

(** Source for [smooth_constant_rank_zero_regression]: regression
    for Federer 3.1.18, pp. 229–230, including both empty coordinate
    blocks and zero source or target dimension. The target derivative
    normalization is retained even for constant maps. *)
Lemma smooth_constant_rank_zero_regression (R:realType) m n (a:R_n R (0+m)) (c:R_n R n) :
  exists (U:set (R_n R (0+m))) (e:R)
    (p:{linear R_n R n->R_n R 0}) (j:{linear R_n R 0->R_n R n})
    (g G:R_n R (0+m)->R_n R (0+m)) (psi:R_n R 0->R_n R n), forall k,
  @is_euclidean_constant_rank_chart R 0 m n k setT (fun _=>c) (fun _=>0)
    a U e p j g G psi.
Proof.
pose X:=R_n R (0+m).
pose Y:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R (0+m)).
pose NY:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R (0+m)).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R n).
have hopen x (hx:setT x):norm_domain_interior NX setT x:=@norm_full_domain_interior R X NX x.
have hf:norm_class_all_orders hNX hNY setT (fun _=>c).
  move=>k; exact (@norm_class_constant R X Y NX NY hNX hNY setT c k hopen).
have hD:=@norm_class_one_constant_field R X Y NX NY hNX hNY setT c hopen.
have hz:has_linear_rank (0:Hom X Y) 0%N.
  apply: (linear_rank_zeroP (0:Hom X Y)).2=>x; exact: hom_zeroE.
have hgen:norm_generic_rank NX setT (fun _=>(0:Hom X Y)) a 0%N.
  exists 1; split; first exact: ltr01.
  by move=>h hh; split.
exact (@federer_3_1_18_smooth R 0 m n setT (fun _=>c) (fun _=>0) a hf hD hgen).
Qed.

(** Regression cases for Federer 3.1.19, p. 231: a genuine
    codimension-one coordinate plane, empty sets in otherwise impossible
    dimensions, and isolated points at class zero. *)
From Federer Require Import ModuleQuotient GrassmannSubspaces EuclideanSubmanifoldUP
  EuclideanCoordinatePlane LinearPlaneSubmanifold SubmanifoldChartsUP SubmanifoldEquivalences
  SubmanifoldBasicLaws ZeroSubmanifold SubmanifoldLocalGeometry.

(** Source for [coordinate_axis_submanifold_regression]: supporting
    example for the full equivalence of 3.1.19, p. 231. The vertical
    coordinate axis is a submanifold and has normalized orthogonal
    graph charts at every positive class. *)
Lemma coordinate_axis_submanifold_regression (R:realType) k : (1<=k)%N ->
  @has_orthogonal_graph_charts R (1+1) 1 k
    [set x|@euclidean_first_block_map R 1 1 x=0].
Proof.
move=>hk.
have [Z hZ]:=@euclidean_last_coordinate_plane R 1 1.
have heq:(grassmann_val Z:set (R_n R (1+1)))=[set x|@euclidean_first_block_map R 1 1 x=0].
  apply/seteqP; split=>x; [exact: (hZ x).1|exact: (hZ x).2].
have hB:=@linear_plane_submanifold R (1+1) 1 k Z.
rewrite heq in hB.
have hEquiv:=@federer_3_1_19 R (1+1) 1 k
  [set x|@euclidean_first_block_map R 1 1 x=0] (leqnn 1) hk.
exact (hEquiv.2.2.2.1 hB).
Qed.

(** Source for [empty_oversized_submanifold_regression]: the empty
    subset has no points requiring a plane in condition (1), 3.1.19,
    p. 231. A local dimension bound must not exclude this case. *)
Lemma empty_oversized_submanifold_regression (R:realType) k :
  @is_euclidean_submanifold R 0 2 k set0.
Proof. exact: empty_euclidean_submanifold. Qed.

(** Source for [isolated_point_class_zero_regression]: the final
    sentence of Federer 3.1.19, p. 231, at the boundary class k=0.
    An arbitrary singleton has actual zero-plane translation charts. *)
Lemma isolated_point_class_zero_regression (R:realType) n (c:R_n R n) :
  @is_euclidean_submanifold R n 0 0 [set c].
Proof.
apply: isolated_points_zero_submanifold=>b hb; split=>//.
exists 1; split; first exact: ltr01.
move=>h hh hc; exact (eq_trans hc (esym hb)).
Qed.

(** Regression examples for Federer 3.1.20, pp. 232–233. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom ModuleQuotient GrassmannSubspaces GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness NormMetric RetractionUP EuclideanCoordinatePlane
  EuclideanBlockLinearMaps LinearPlaneSubmanifold SubmanifoldBasicLaws SubmanifoldNeighbourhoodRetraction NeighbourhoodRetractionTheorem.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [axis_neighbourhood_retraction_regression]: a
    codimension-one plane exercises the constructed forward implication
    of Federer 3.1.20, pp. 232–233, including the strengthened boundary
    class zero; no chosen retraction is assumed. *)
Lemma axis_neighbourhood_retraction_regression (R:realType) k :
  exists (A:set (R_n R (1+1))) (f:R_n R (1+1)->R_n R (1+1)),
    @open [the topologicalType of real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R (1+1)))] A /\
    is_norm_class_retraction (inner_norm_real_norm (@euclidean_inner_productP R (1+1)))
      A [set x|@euclidean_first_block_map R 1 1 x=0] f k.
Proof.
have [Z hZ]:=@euclidean_last_coordinate_plane R 1 1.
have heq:(grassmann_val Z:set (R_n R (1+1)))=[set x|@euclidean_first_block_map R 1 1 x=0].
  apply/seteqP; split=>x; [exact: (hZ x).1|exact: (hZ x).2].
have hB:=@linear_plane_submanifold R (1+1) 1 k Z.
rewrite heq in hB.
exact: submanifold_neighbourhood_retraction hB.
Qed.

(** Source for [empty_retraction_characterization_regression]: the
    connected empty set in Federer 3.1.20, p. 232, has a genuine
    neighbourhood retraction even in zero ambient dimension. *)
Lemma empty_retraction_characterization_regression (R:realType) k : (1<=k)%N ->
  exists (A:set (R_n R 0)) (f:R_n R 0->R_n R 0),
    @open [the topologicalType of real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R 0))] A /\
    is_norm_class_retraction (inner_norm_real_norm (@euclidean_inner_productP R 0)) A set0 f k.
Proof.
move=>hk.
have hC:@connected [the topologicalType of real_norm_metric_space
  (inner_norm_real_norm (@euclidean_inner_productP R 0))] set0:=@connected0 _.
have hT:=@federer_3_1_20 R 0 k set0 hk hC.
apply: hT.1; exists 2%N; exact: empty_euclidean_submanifold.
Qed.

(** Regression examples for Federer 3.1.21, pp. 233–234. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom ModuleQuotient GrassmannSubspaces GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness NormMetric NormDifferentialUP NormFiniteLinearBound
  EuclideanBlockLinearMaps EuclideanCoordinatePlane LinearPlaneSubmanifold EuclideanSubmanifoldUP
  TangentConeUP TangentConeBasic TangentLinearFibre EuclideanBundleUP SubmanifoldTangentBundle SubmanifoldNormalBundle.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [axis_tangent_cone_regression]: supporting the
    tangent-plane assertion of Federer 3.1.21, p. 234.
    The tangent of the vertical coordinate axis at zero is
    exactly that axis, using the affine-fibre theorem. *)
Lemma axis_tangent_cone_regression (R:realType) :
  norm_tangent_cone (inner_norm (@euclidean_inner_productP R (1+1)))
    [set x|@euclidean_first_block_map R 1 1 x=0] 0=
    [set x|@euclidean_first_block_map R 1 1 x=0].
Proof.
pose X:=R_n R (1+1).
pose Y:=R_n R 1.
pose NX:=inner_norm (@euclidean_inner_productP R (1+1)).
pose NY:=inner_norm (@euclidean_inner_productP R 1).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R (1+1)).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R 1).
pose r:=@euclidean_first_block_map R 1 1.
have hb:=@norm_finite_linear_bounded R X Y NX NY hNX hNY (1+1)
  (@coordinate_basis R (1+1)) (@coordinate_basisP R (1+1)) r.
have he:=@norm_tangent_linear_fibre R X Y NX NY hNX hNY r 0 hb.
by rewrite linear0 in he.
Qed.

(** Source for [axis_bundle_class_zero_regression]: the boundary
    regularity k-1=0 in both bundle assertions of Federer
    3.1.21, p. 234. A class-one line in R^2
    has two-dimensional tangent and normal bundles of class zero
    in R^4, using actual straightening charts. *)
Lemma axis_bundle_class_zero_regression (R:realType) :
  @is_euclidean_submanifold R ((1+1)+(1+1)) (1+1) 0
    (@euclidean_tangent_bundle R (1+1) [set x|@euclidean_first_block_map R 1 1 x=0]) /\
  @is_euclidean_submanifold R ((1+1)+(1+1)) (1+1) 0
    (@euclidean_normal_bundle R (1+1) [set x|@euclidean_first_block_map R 1 1 x=0]).
Proof.
have [Z hZ]:=@euclidean_last_coordinate_plane R 1 1.
have heq:(grassmann_val Z:set (R_n R (1+1)))=[set x|@euclidean_first_block_map R 1 1 x=0].
  apply/seteqP; split=>x; [exact: (hZ x).1|exact: (hZ x).2].
have hB:=@linear_plane_submanifold R (1+1) 1 1 Z.
rewrite heq in hB.
split.
- exact (@submanifold_tangent_bundle R (1+1) 1 0 _ hB).
- exact (@submanifold_normal_bundle R (1+1) 1 0 _ hB).
Qed.

(** Source for [empty_tangent_cone_regression]: the closure
    condition in Federer 3.1.21, p. 233, including a
    zero-dimensional ambient space. The tangent cone of the
    empty set is empty, rather than a forced singleton zero. *)
Lemma empty_tangent_cone_regression (R:realType) n (a:R_n R n) :
  norm_tangent_cone (inner_norm (@euclidean_inner_productP R n)) set0 a=set0.
Proof.
pose X:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose M:=real_norm_metric_space hNX.
apply/seteqP; split=>v; last by case.
move=>hv.
have hc:=@norm_tangent_base_closure R X NX hNX set0 a v hv.
exact (@closed0 M a hc).
Qed.

(** Source for [relative_isolated_base_value_regression]: the need
    for f(a)=eta in Federer 3.1.22, p. 235, as
    corrected by the erratum p. 4, book p. 235 line 19.
    At an isolated point the punctured remainder is vacuous,
    so it cannot by itself fix the base value of the extension. *)
Lemma relative_isolated_base_value_regression (R:realType) :
  (forall e:R,0<e -> exists d:R,0<d /\ forall x:R,
    x=0 -> 0<`|x| -> `|x|<d -> `|1-(0:R)|<=e*`|x|) /\
  ~ @has_relative_first_order_approximation R R^o R^o (fun t=>`|t|) (fun t=>`|t|)
    setT [set 0] (fun _=>1) 0 0 0.
Proof.
split.
- move=>e he; exists 1; split; first exact: ltr01.
  by move=>x ->; rewrite normr0 ltxx.
- move=>[_ [hbase _]].
  have hbad:=hbase (erefl (0:R)); move: hbad.
  by move/eqP; rewrite oner_eq0.
Qed.

(** Source for [relative_boundary_outside_domain_regression]: the
    condition a in Clos S, rather than a in S, in
    Federer 3.1.22, p. 235. A constant map on
    the open positive half-line has a relative differential at zero,
    although zero is outside its actual domain. The sealed graph
    records this differential without inventing an original function value. *)
Lemma relative_boundary_outside_domain_regression (R:realType) :
  ~ (0<(0:R)) /\
  partial_function_domain (@relative_norm_differential R R^o R^o
    (fun t=>`|t|) (fun t=>`|t|) (scalar_absolute_value_norm R) (scalar_absolute_value_norm R)
    [set x|0<x] [set x|0<x] (fun _=>0)) 0.
Proof.
split; first by rewrite ltxx.
pose N:=fun t:R^o=>`|t|.
pose hN:=scalar_absolute_value_norm R.
pose S:set R^o:=fun x=>0<x.
have hcl:@closure (real_norm_metric_space hN) S 0.
  apply: (@norm_closure_balls R R^o N hN S 0).2=>e he.
  have hp:0<e/2 by rewrite divr_gt0 // ltr0n.
  exists (e/2); split; first exact hp.
  rewrite /N subr0 (ger0_norm (ltW hp)); by lra.
have [L hL]:=@tangent_differential_restriction_exists R R^o R^o N S 0 0.
exists L; apply: (@relative_norm_differential_graph R R^o R^o N N hN hN S S (fun _=>0) 0 L).2.
split; first exact hcl.
exists setT,(fun _=>0),0; split.
- exact (@norm_differential_constant R R^o R^o N N hN hN setT 0 0 (norm_full_domain_interior N 0)).
- split=>// x hx _; by split.
Qed.

(** Source for [relative_empty_class_zero_extension_regression]: the
    empty-subset and class-zero boundaries of the global extension
    assertion in Federer 3.1.22, p. 236. The actual
    original domain may be empty, and the ambient dimension may be zero. *)
Lemma relative_empty_class_zero_extension_regression (R:realType) n
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY) (f:R_n R n->Y) :
  exists g,@is_norm_relative_extension R (R_n R n) Y
    (inner_norm (@euclidean_inner_productP R n)) NY
    (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY set0 set0 f 0 setT g.
Proof.
apply: euclidean_closed_relative_class_extension; first exact: closed0.
by move=>a [].
Qed.

(** Source for [whole_space_unit_control_regression]: a flat
    boundary example for Federer 3.1.23, pp. 236–237.
    On the whole space identity already satisfies unit Lipschitz
    control t=1, for every class and centre, including class zero.
    This does not remove the strict t<1 hypothesis for general B. *)
Lemma whole_space_unit_control_regression (R:realType) n k (b:R_n R n) (r:R) :
  0<r -> is_controlled_tangent_straightening
    (inner_norm_real_norm (@euclidean_inner_productP R n)) setT b 1 r
    (fun x=>x) (fun x=>x) k.
Proof.
move=>hr.
pose X:=R_n R n.
pose N:=inner_norm (@euclidean_inner_productP R n).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose Id:=hom_of_linear (linear_id X).
have hId:norm_bounded_linear N N Id.
  exists 1; split; first exact: ler01.
  by move=>v; rewrite /Id hom_of_linearE /= mul1r.
constructor.
- exact (@norm_linear_diffeomorphism R X X N N hN hN Id Id k hId hId
    (fun x=>erefl x) (fun x=>erefl x)).
- by move=>x y; rewrite invr1 mul1r.
- by move=>x y; rewrite invr1 mul1r.
- by move=>x hx.
- move=>x hx; rewrite (@norm_tangent_open_domain R X N hN setT b
    (norm_full_domain_interior N b)); by [].
Qed.

(** Source for [singleton_supported_straightening_regression]: the
    zero-dimensional submanifold case of Federer 3.1.23,
    pp. 236–237, in arbitrary ambient dimension and
    at an arbitrary translated point. The actual chart and
    supported diffeomorphism are supplied by the proved theorem. *)
Lemma singleton_supported_straightening_regression (R:realType) n k (c:R_n R n) :
  (1<=k)%N -> exists rho:R,0<rho /\ forall r:R,0<r -> r<rho -> exists F g,
    is_controlled_tangent_straightening
      (inner_norm_real_norm (@euclidean_inner_productP R n)) [set c] c (1/2) r F g k.
Proof.
move=>hk.
have hB:@is_euclidean_submanifold R n 0 k [set c].
  apply: isolated_points_zero_submanifold=>b hb; split=>//.
  exists 1; split; first exact: ltr01.
  move=>h hh hc; exact (eq_trans hc (esym hb)).
have ht:0<(1/2:R)<1 by apply/andP; split; lra.
exact (@federer_3_1_23 R n 0 k [set c] c (1/2) hk hB (erefl c) ht).
Qed.

(** Source for [zero_ambient_supported_straightening_regression]:
    the singleton ambient vector space in Federer 3.1.23,
    pp. 236–237. This exercises the complete cutoff,
    graph, global inverse and exact-plane construction with both
    ambient and manifold dimensions zero. *)
Lemma zero_ambient_supported_straightening_regression (R:realType) :
  exists rho:R,0<rho /\ forall r:R,0<r -> r<rho -> exists F g,
    is_controlled_tangent_straightening
      (inner_norm_real_norm (@euclidean_inner_productP R 0)) setT 0 (1/2) r F g 1%N.
Proof.
have hB:@is_euclidean_submanifold R 0 0 1 setT.
  apply: isolated_points_zero_submanifold=>b hb; split=>//.
  exists 1; split; first exact: ltr01.
  move=>h hh hc; by rewrite (coordinate_zero (b+h)) (coordinate_zero b).
have ht:0<(1/2:R)<1 by apply/andP; split; lra.
exact (@federer_3_1_23 R 0 0 1 setT 0 (1/2) (leqnn 1%N) hB Logic.I ht).
Qed.

(** Source for [analytic_inverse_translation_without_completeness_regression]:
    the inverse assertion in Federer 3.1.24, pp. 239–240, on an
    arbitrary normed space. The inverse translation is analytic and
    the forward map only needs class one; no completeness or finite
    dimension assumption is supplied to the inverse theorem. *)
Example analytic_inverse_translation_without_completeness_regression
    (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX) (b:X) :
  @norm_analytic R X X NX NX hNX hNX setT (fun x=>x+b).
Proof.
have hD:=@norm_translation_diffeomorphism R X NX hNX b 1%N.
have hOpen x (_:True):norm_domain_interior NX setT x:=norm_full_domain_interior NX x.
have hminus:=(@norm_translations_analytic R X NX hNX setT hOpen b).2.
apply:(@norm_analytic_inverse_from_first R X X NX NX hNX hNX setT setT
  (fun x=>x+b) (fun y=>y-b) (fun _ _=>Logic.I) (fun _ _=>Logic.I) _ _
  (norm_diffeomorphism_inverse_class hD) hminus).
- by move=>x _; rewrite addrK.
- by move=>y _; rewrite subrK.
Qed.

(** Source for [singleton_analytic_submanifold_regression]: the
    analytic version of the isolated-point equivalence in 3.1.19,
    asserted by 3.1.24, p. 240. An arbitrarily translated singleton
    is an analytic zero-dimensional submanifold in every ambient
    dimension, including zero. *)
Example singleton_analytic_submanifold_regression (R:realType) n (b:R_n R n) :
  @is_euclidean_analytic_submanifold R n 0 [set b].
Proof.
apply:isolated_points_zero_analytic_submanifold=>a ha; split; first exact ha.
exists 1; split; first exact:ltr01.
move=>h hh hb; exact (eq_trans hb (esym ha)).
Qed.

(** Source for [empty_analytic_manifold_large_dimension_regression]:
    the empty-set boundary of the analytic chart equivalence in
    Federer 3.1.24, p. 240. The regular-level formulation must
    retain the empty set even when its requested dimension exceeds
    the ambient dimension; its codimension bounds are local. *)
Example empty_analytic_manifold_large_dimension_regression (R:realType) n :
  @has_analytic_regular_level_charts R n n.+1 set0 /\
  @has_analytic_orthogonal_graphs R n n.+1 set0.
Proof.
have hB:@is_euclidean_analytic_submanifold R n n.+1 set0 by move=>b hb; case:hb.
have [h12 [_ [_ h15]]]:=@federer_3_1_19_analytic R n n.+1 set0.
split; [exact (h12.1 hB)|exact (h15.1 hB)].
Qed.

(** Source for [analytic_unbounded_constant_term_regression]: the
    local correction to the absolute-series estimate in Federer
    3.1.24, p. 241. The analytic constant two violates the printed
    degree-zero bound for every proposed analytic constant. *)
Example analytic_unbounded_constant_term_regression (R:realType) (c:R) :
  @norm_analytic_at R R^o R^o (fun t=>`|t|) (fun t=>`|t|)
    (scalar_absolute_value_norm R) (scalar_absolute_value_norm R) setT (fun _=>2) 0 /\
  ~(`|2:R|<=c^+0*(0:R)^+0).
Proof. exact (analytic_printed_constant_term_bound_fails c). Qed.

(** Source for [zero_degree_jacobian_in_zero_ambient_regression]:
    the nonnegative degree convention of Federer 3.2.1, p. 241.
    On the singleton ambient space the actual ordinary differential
    exists and its zeroth exterior power has norm one. *)
Example zero_degree_jacobian_in_zero_ambient_regression (R:realType) n (c:R_n R n) :
  partial_function_graph (@euclidean_jacobian R 0 n 0 setT (fun _=>c)) 0 1.
Proof.
apply:(euclidean_jacobian_graph 0 setT (fun _:R_n R 0=>c) 0 1).2.
exists 0; split.
- exact (@norm_differential_constant R (R_n R 0) (R_n R n)
    (inner_norm (@euclidean_inner_productP R 0)) (inner_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R 0)) (inner_norm_real_norm (@euclidean_inner_productP R n))
    setT 0 c (norm_full_domain_interior _ _)).
- exact:euclidean_linear_jacobian_zero_degree.
Qed.

(** Source for [empty_domain_zero_degree_jacobian_regression]:
    the whenever differentiable clause in Federer 3.2.1, p. 241.
    The zeroth-degree value one is not assigned to a point outside
    the actual differential domain, even for a constant map. *)
Example empty_domain_zero_degree_jacobian_regression (R:realType) m n (c:R_n R n) (a:R_n R m) :
  ~partial_function_domain (@euclidean_jacobian R m n 0 set0 (fun _=>c)) a.
Proof.
move=>/(euclidean_jacobian_domain 0 set0 (fun _:R_n R m=>c) a) [L hL].
exact (@norm_domain_interior_member R (R_n R m) (inner_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R m)) set0 a (norm_differential_interior hL)).
Qed.

(** Source for [zero_source_approximate_jacobian_domain_regression]:
    the approximate Jacobian definition of Federer 3.2.1, p. 241,
    retains the zero-source punctured-density convention documented
    for 3.1.2. Its approximate differential domain is empty, in
    every exterior degree, including zero. *)
Example zero_source_approximate_jacobian_domain_regression (R:realType) n k
    (A:R_n R 0->Prop) (f:R_n R 0->R_n R n) (a:R_n R 0) :
  ~partial_function_domain (approximate_jacobian k A f) a.
Proof.
move=>/(approximate_jacobian_domain k A f a) [L hL].
exact (@zero_dimensional_no_approximate_differential R (R_n R n)
  (inner_norm (@euclidean_inner_productP R n)) A f a L hL).
Qed.

(** Source for [zero_source_borel_cover_regression]: the
    zero-dimensional source boundary of Federer 3.2.2,
    p. 242. The complete inverse and Jacobian piece
    laws hold for every constant value in every target. *)
Example zero_source_borel_cover_regression (R:realType) n (c:R_n R n) lambda:
  1<lambda -> exists G,is_injective_differential_cover (fun _:R_n R 0=>c) lambda G.
Proof.
move=>hl; apply:federer_3_2_2 hl; exact:cst_continuous.
Qed.

(** Source for [zero_target_injective_locus_empty_regression]:
    the empty-locus case of Federer 3.2.2, p. 242,
    when the positive-dimensional source exceeds the target.
    The theorem needs no dimension inequality hypothesis. *)
Example zero_target_injective_locus_empty_regression (R:realType) m
    (f:R_n R m.+1->R_n R 0):injective_differential_locus f=set0.
Proof.
apply/seteqP; split=>a; last by case.
move=>[D [hD hInj]].
have he:D (@coordinate_basis R m.+1 ord0)=D 0 by rewrite (coordinate_zero (D (@coordinate_basis R m.+1 ord0))) (coordinate_zero (D 0)).
have hb:=hInj _ _ he.
have hh:=congr1 (fun v:R_n R m.+1=>v ord0) hb.
by move:hh; rewrite /coordinate_basis !ffunE eqxx=>/eqP; rewrite oner_eq0.
Qed.

From Federer Require Import PartialFunctionBasic PositiveCharacteristicMeasurability NumericalSum
  ExtendedRealOrderTopology MeasureIntegralUP PartialDensityProduct HausdorffMeasure LipschitzUP.
Local Open Scope ereal_scope.

(** Source for [empty_fibre_partial_sum_regression]: the inner
    sum in Federer 3.2.3(2), p. 243, with the empty
    sum convention of 2.1.1, p. 52. An empty fibre
    has sum zero even for an everywhere undefined integrand. *)
Example empty_fibre_partial_sum_regression (R:realType):
  partial_function_graph (partial_fibre_numerical_sum (fun _:bool=>false)
    (@partial_function_empty bool (extended_real_line R))) true 0.
Proof.
apply/partial_fibre_numerical_sum_graph; exists (fun _=>0); split.
- move=>x hImpossible; discriminate hImpossible.
have he:[set x:bool|false=true]=set0.
  apply/seteqP; split=>x; last by case.
  move=>hImpossible; discriminate hImpossible.
by rewrite he numerical_sum_empty.
Qed.

(** Source for [undefined_nonempty_fibre_regression]: the exact
    domain of the inner sum in Federer 3.2.3(2), p. 243.
    An undefined summand is never silently replaced by zero. *)
Example undefined_nonempty_fibre_regression (R:realType):
  ~partial_function_domain (partial_fibre_numerical_sum (fun _:bool=>false)
    (@partial_function_empty bool (extended_real_line R))) false.
Proof.
move=>[z /partial_fibre_numerical_sum_graph [w [hw _]]].
exact (hw true (erefl false)).
Qed.

(** Source for [infinite_integrand_weighted_area_regression]: the
    integrability rather than summability premise of Federer
    3.2.3(2), p. 243. Apply the full weighted theorem
    to the positive-infinite integrand, with zero-infinity
    multiplication and exact fibre domains retained. *)
Example infinite_integrand_weighted_area_regression (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)):
  is_metric_lipschitz setT f ->
  exists a,is_measure_integral (@euclidean_lebesgue_measure R m)
      (partial_density_product (partial_function_total (fun _:R_n R m=>(+oo:extended_real_line R)))
        (extended_euclidean_jacobian f)) a /\
    is_measure_integral (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
      (partial_fibre_numerical_sum f (partial_function_total (fun _:R_n R m=>(+oo:extended_real_line R)))) a.
Proof.
move=>hLip; apply:euclidean_weighted_area_formula hLip _.
exists (+oo*euclidean_lebesgue_measure m setT).
exact (nonnegative_extended_constant_integral (euclidean_lebesgue_is_measure R m) (leey 0)).
Qed.

From mathcomp Require Import cardinality.
From Federer Require Import BorelFunctionBasic.

(** Source for [zero_source_positive_jacobian_locus_regression]:
    the positive-Jacobian condition of Federer 3.2.4, p. 244,
    on a zero-dimensional source. The empty exterior product
    has Jacobian one, so the locus is the whole singleton space. *)
Example zero_source_positive_jacobian_locus_regression (R:realType) n (c:R_n R n):
  positive_euclidean_jacobian_locus (fun _:R_n R 0=>c)=setT.
Proof.
apply/seteqP; split=>x _; first exact:Logic.I.
exists 1%R; split; last exact:ltr01.
rewrite (coordinate_zero x); exact (zero_degree_jacobian_in_zero_ambient_regression c).
Qed.

(** Source for [empty_borel_selection_family_regression]: the empty
    cover case of the Borel selection in Federer 3.2.4,
    p. 244. No nonexistent cover member is selected. *)
Example empty_borel_selection_family_regression (X:topologicalType):
  exists B:set X,borel_set B /\ B=set0 /\ (@id X) @` B=set0.
Proof.
have hCount:countable (@set0 (set X)):=countable0 (set X).
have hB:forall E:set X,set0 E -> borel_set E by move=>E [].
have hI:forall E:set X,set0 E -> forall x y,E x -> E y -> (@id X) x=(@id X) y -> x=y.
  by move=>E [].
have hImage:forall E:set X,set0 E -> borel_set ((@id X) @` E) by move=>E [].
have [B [hb [hSub [hInj hEq]]]]:=borel_univalent_countable_selection
  (@identity_borel_function X) hCount hB hI hImage.
have hEmpty:B=set0.
  apply/seteqP; split=>x; last by case.
  by move=>hx; have [E []]:=hSub x hx.
exists B; split=>//; split=>//; rewrite hEmpty.
apply/seteqP; split=>x; last by case.
by move=>[y []].
Qed.

From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialDensityProduct
  EuclideanJacobianMeasurable MeasureUP MeasureBasic MeasureSplit MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP
  LipschitzUP LipschitzBasic HausdorffMeasure MappingMultiplicity MappingMultiplicityLaws MappingPartitionMultiplicity
  CharacteristicFunctionUP CharacteristicFunctionSealed NullSubsetIntegral AreaIntegralTransformation AreaTransformIntegrands.

(** Source for [empty_area_transform_arbitrary_weight_regression]:
    condition (2) of Federer 3.2.5, pp. 244–245,
    on an empty source set. The weight is arbitrary and
    no target measurability premise is supplied. Both
    actual integrals exist with value zero. *)
Example empty_area_transform_arbitrary_weight_regression (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (g:R_n R n->real_line_metric R):
  (m<=n)%N -> is_metric_lipschitz setT f ->
  is_measure_integral (@euclidean_lebesgue_measure R m) (area_transform_source_integrand f set0 g) 0 /\
    is_measure_integral (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
      (area_transform_target_integrand f set0 g) 0.
Proof.
move=>hmn hLip.
have hm:=euclidean_lebesgue_is_measure R m.
have hb:=@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R n)) m.
have hSource:is_measure_integral (@euclidean_lebesgue_measure R m) (area_transform_source_integrand f set0 g) 0.
  exact (@null_target_subset_integral R _ _
    (partial_density_product (partial_function_total (fun x=>(g (f x))%:E:extended_real_line R))
      (extended_euclidean_jacobian f)) set0 hm (measure_empty hm)).
have hFinite:measure_almost_everywhere
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
    [set y|@mapping_multiplicity R _ _ f set0 y< +oo].
  apply:(@measure_almost_everywhere_mono R _ _ hb setT _ _ (measure_almost_everywhere_true hb))=>y _.
  have hZero:@mapping_multiplicity R _ _ f set0 y=0.
    apply:((@mapping_multiplicity_zero_iff R _ _ f set0 y).2).
    by move=>[x []].
  change (is_true (@mapping_multiplicity R _ _ f set0 y< +oo)).
  by rewrite hZero ltry.
have hAlt:has_area_transform_alternative f set0 g by right; left.
split; first exact hSource.
exact ((federer_3_2_5 hmn hLip (measure_measurable_empty hm) hAlt 0).1 hSource).
Qed.

(** Source for [zero_source_area_transform_arbitrary_weight_regression]:
    the zero-dimensional boundary of Federer 3.2.5(2),
    pp. 244–245. Multiplicity is finite on every fibre
    of a map from R^0, so an arbitrary ambient weight
    satisfies the transformation formula without target
    measurability or source summability assumptions. *)
Example zero_source_area_transform_arbitrary_weight_regression (R:realType) n (c:R_n R n)
    (g:R_n R n->real_line_metric R) (a : \bar R):
  is_measure_integral (@euclidean_lebesgue_measure R 0)
      (area_transform_source_integrand (fun _:R_n R 0=>c) setT g) a <->
    is_measure_integral (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) 0)
      (area_transform_target_integrand (fun _:R_n R 0=>c) setT g) a.
Proof.
pose X:=inner_metric_space (@euclidean_inner_productP R 0).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose f:=fun _:X=>(c:Y).
have hLip:is_metric_lipschitz setT f.
  apply:metric_lipschitz_of_bound.
  exact (least_metric_lipschitz_bound (@metric_lipschitz_constant_map R X Y setT c)).
have hInj:{in (@setT X) &,injective f}.
  move=>x y _ _ _; by rewrite (coordinate_zero x) (coordinate_zero y).
pose chi:=@CharacteristicFunction.value R Y (f @` setT).
have hChi:is_characteristic_function (f @` setT) chi:=@CharacteristicFunction.laws R Y (f @` setT).
have hb:=@hausdorff_measure_is_measure R Y 0.
have hFinite:measure_almost_everywhere (@hausdorff_measure R Y 0)
    [set y|@mapping_multiplicity R X Y f setT y< +oo].
  apply:(@measure_almost_everywhere_mono R Y _ hb setT _ _ (measure_almost_everywhere_true hb))=>y _.
  change (is_true (@mapping_multiplicity R X Y f setT y< +oo)).
  rewrite (@injective_mapping_multiplicity_characteristic R X Y f setT chi hInj hChi y).
  exact:ltry.
have hAlt:has_area_transform_alternative f setT g by right; left.
exact (federer_3_2_5 (leq0n n) hLip (measure_measurable_whole (euclidean_lebesgue_is_measure R 0)) hAlt a).
Qed.

From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
 RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialZeroExtension PartialDensityProduct
 NormedCurveDerivativeUP NormedCurveDerivativeIntegrands MetricCurveAbsoluteContinuityUP LocallyAbsolutelyContinuousCurve
 EuclideanCurveSpeedMeasure EuclideanCurveAreaIntegrands AbsoluteContinuousCurveArea CoveringFamilyUP
 MeasureUP MeasureBasic MeasureFiniteClosure MeasureSplit MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureConullZeroIntegral
 NullSubsetIntegral LebesgueScalarMeasure HausdorffMeasure.
(** Source for [null_source_curve_area_arbitrary_weight_regression]:
    the null-source case in the proof of Federer 3.2.6,
    p. 246. No derivative-existence hypothesis is imposed
    on the null source set; both weighted integrals are zero. *)
Example null_source_curve_area_arbitrary_weight_regression (R:realType) n
    (f:R->inner_metric_space (@euclidean_inner_productP R n)) (A:set (real_line_metric R))
    (g:R_n R n->real_line_metric R):
  is_locally_absolutely_continuous_curve f -> metric_set_bounded A -> lebesgue_scalar_measure A=0 ->
  is_measure_integral (@lebesgue_scalar_measure R) (curve_area_source_integrand f A g) 0 /\
    is_measure_integral (@hausdorff_measure R [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] 1)
      (curve_area_target_integrand f A g) 0.
Proof.
move=>hAC hBound hNull.
have hm:=lebesgue_scalar_is_measure R.
have hS:is_measure_integral (@lebesgue_scalar_measure R) (curve_area_source_integrand f A g) 0.
  exact (@null_target_subset_integral R [the choiceType of real_line_metric R] (@lebesgue_scalar_measure R)
    (partial_density_product (partial_function_total (fun x=>(g (f x))%:E:extended_real_line R))
      (euclidean_curve_speed f)) A hm hNull).
split; first exact hS.
exact ((federer_3_2_6_1 g hAC hBound (measure_null_measurable hm hNull) 0).1 hS).
Qed.

(** Source for [zero_target_curve_area_arbitrary_weight_regression]:
    the singleton target boundary of the first equation in
    Federer 3.2.6, p. 245. A constant curve has zero
    actual speed everywhere, including on the source set A.
    Arbitrary real weights are retained without measurability. *)
Example zero_target_curve_area_arbitrary_weight_regression (R:realType)
    (A:set (real_line_metric R)) (g:R_n R 0->real_line_metric R):
  metric_set_bounded A -> measure_measurable (@lebesgue_scalar_measure R) A ->
  is_measure_integral (@lebesgue_scalar_measure R)
    (curve_area_source_integrand (fun _:R=>(0%R:R_n R 0)) A g) 0 /\
  is_measure_integral (@hausdorff_measure R [the metricType R of inner_metric_space (@euclidean_inner_productP R 0)] 1)
    (curve_area_target_integrand (fun _:R=>(0%R:R_n R 0)) A g) 0.
Proof.
move=>hBound hA.
pose Y:=inner_metric_space (@euclidean_inner_productP R 0).
pose f:=fun _:R=>(0%R:Y).
have hAC:is_locally_absolutely_continuous_curve f.
  move=>a b hab e he; exists 1%R; split; first exact:ltr01.
  move=>s hs hLen.
  have hZero:metric_interval_family_increment_sum f s=0%R.
    rewrite /metric_interval_family_increment_sum; apply:big1=>p _; exact:mdistxx.
  rewrite hZero; exact:ltW he.
have hm:=lebesgue_scalar_is_measure R.
have hS:is_measure_integral (@lebesgue_scalar_measure R) (curve_area_source_integrand f A g) 0.
  apply:(measure_almost_zero_integral hm).
  apply:(@measure_almost_everywhere_mono R [the choiceType of real_line_metric R]
    (@lebesgue_scalar_measure R) hm _ _ _ (measure_almost_everywhere_true hm))=>x _.
  case:(pselect (A x))=>hx.
  - apply/partial_function_zero_extension_graph; left; split=>//.
    apply/partial_density_product_graph; exists (g (f x))%:E,0.
    split=>//; split; last exact:mule0.
    exists (0%R:R_n R 0); split.
    + exact (constant_normed_curve_derivative (inner_norm_real_norm (@euclidean_inner_productP R 0)) (0%R:R_n R 0) x).
    + by rewrite inner_norm0.
  - apply/partial_function_zero_extension_graph; right; by split.
split; first exact hS.
exact ((federer_3_2_6_1 g hAC hBound hA 0).1 hS).
Qed.

(** Federer (1969), 3.2.6, pp. 245–246:
    regression for equal endpoint values, retained by the
    erratum's weak endpoint inequality. Every real weight
    is allowed on a constant curve. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground LocallyAbsolutelyContinuousCurve MetricCurveAbsoluteContinuityBasic
  ScalarAbsoluteContinuousArea ScalarSignedSourceSplitting ScalarSignedMultiplicityAlmost ScalarSignedSubstitutionIntegrals
  EndpointLevelSigns PartialFunctionUP PartialFunctionBasic MappingMultiplicity CountingMeasure
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralUniqueness
  MeasureConullZeroIntegral LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [constant_curve_signed_substitution_regression]:
    equal-endpoint boundary of Federer 3.2.6,
    pp. 245–246, erratum p. 4. Full multiplicity
    can be infinite at the constant image point, but
    its product with any real g is zero almost
    everywhere. The signed source integral is zero. *)
Example constant_curve_signed_substitution_regression (R:realType) (c:R) (g:R->R) (a b:R):
  a<b ->
  is_measure_integral (@lebesgue_scalar_measure R)
    (scalar_signed_substitution_source (fun _=>c) g a b) 0%E.
Proof.
move=>hab; have hm:=lebesgue_scalar_is_measure R.
pose f:=fun _:R=>c.
have hAC:is_locally_absolutely_continuous_curve (f:R->real_line_metric R).
  move=>u v huv; exact (@constant_metric_curve_absolutely_continuous R [the metricType R of real_line_metric R] c u v).
have hMult:is_measure_integral (@lebesgue_scalar_measure R)
    (scalar_curve_area_target_integrand f `[a,b] g) 0%E.
  apply:(measure_almost_zero_integral hm).
  have hOff:measure_almost_everywhere (@lebesgue_scalar_measure R) (~` [set c]).
    by rewrite /measure_almost_everywhere setCK lebesgue_scalar_singleton.
  apply:(@measure_almost_everywhere_mono R [the choiceType of real_line_metric R]
    (@lebesgue_scalar_measure R) hm _ _ _ hOff)=>y hy.
  have he:mapping_fibre f (`[a,b]:set (real_line_metric R)) y=set0.
    apply/seteqP; split; first by move=>x [_ hcy]; exfalso; apply:hy; by rewrite /f in hcy; rewrite -hcy.
    by move=>x [].
  change (((g y)%:E * @counting_measure R [the choiceType of real_line_metric R]
    (mapping_fibre f (`[a,b]:set (real_line_metric R)) y))%E=0%E).
  by rewrite he (measure_empty (counting_measure_is_measure R _)) mule0.
have hSum:is_measure_summable (@lebesgue_scalar_measure R) (scalar_curve_area_target_integrand f `[a,b] g).
  by exists 0%R.
have [z [hS hT]]:=scalar_signed_substitution_finite_integrals hAC hab hSum.
have hZero:is_measure_integral (@lebesgue_scalar_measure R) (scalar_oriented_interval_integrand g c c) 0%E.
  apply:(measure_almost_zero_integral hm).
  apply:(@measure_almost_everywhere_mono R [the choiceType of real_line_metric R]
    (@lebesgue_scalar_measure R) hm _ _ _ (measure_almost_everywhere_true hm))=>y _.
  change ((g y*oriented_level_indicator c c y)%:E=0%E).
  by rewrite /oriented_level_indicator subrr mulr0.
have hz:z%:E=0%E:=measure_integral_unique hT hZero.
by rewrite hz in hS.
Qed.

(** Federer (1969), 3.2.7, p. 246: regression
    at an extremal sine level, which lies on
    the boundary of the closed principal branch.
    The branch has one root while the full
    periodic sine has infinitely many roots. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology normedtype lra.
From Federer Require Import RealMetricBackground MappingMultiplicity CountingInjectionBound
  RealTrigonometrySealed RealTrigonometryBasic SineMultiplicity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [sine_endpoint_multiplicity_regression]:
    endpoint check for the first example in
    Federer 3.2.7, p. 246. Both signs of
    the extremal level are included, testing the
    principal closed interval and full periodic fibre. *)
Example sine_endpoint_multiplicity_regression (R:realType) (y:R):
  (y= 1 \/ y= -1) ->
  (@mapping_multiplicity R [the choiceType of real_line_metric R] R
    (@RealTrigonometry.sine R) setT y=+oo)%E /\
  (@mapping_multiplicity R [the choiceType of real_line_metric R] R
    (@RealTrigonometry.sine R) (@sine_principal_source_interval R) y= 1)%E.
Proof.
move=>hy.
have hL:(-1:R)<=y by case:hy=>->; lra.
have hU:y<=(1:R) by case:hy=>->; lra.
split; first exact:real_sine_full_multiplicity hL hU.
rewrite /mapping_multiplicity /sine_principal_source_interval
  (real_sine_principal_branch_fibre hL hU).
exact:counting_measure_singleton_value.
Qed.

(** Federer (1969), 3.2.8, p. 247: the
    almost-everywhere qualification cannot be removed.
    The plane axis projection is its own
    left inverse on the axis, but its
    two actual differentials compose to the projection,
    which is not the plane identity. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm
  HilbertFormCompactness PlaneAxisProjection NormDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [projection_left_inverse_pointwise_failure_regression]:
    necessary almost-everywhere scope in Federer 3.2.8,
    p. 247. At zero the actual projection
    differentials exist and the map is a left
    inverse, yet their composition is not identity. *)
Example projection_left_inverse_pointwise_failure_regression (R:realType):
  @plane_axis_projection R (@plane_axis_projection R 0)=0 /\
  has_norm_differential (inner_norm (@euclidean_inner_productP R 2))
    (inner_norm (@euclidean_inner_productP R 2)) setT (@plane_axis_projection R) 0
      (@plane_axis_projection R) /\
  hom_comp (@plane_axis_projection R) (@plane_axis_projection R)<>
    hom_of_linear (linear_id (R_n R 2)).
Proof.
split; first by rewrite !linear0.
split; first exact:plane_axis_projection_differential.
move=>he.
pose j:'I_2:=Ordinal (erefl (1<2)%N).
have hh:=congr1 (fun L:Hom (R_n R 2) (R_n R 2)=>L (@coordinate_basis R 2 j)) he.
have hZero:@plane_axis_projection R (@coordinate_basis R 2 j)=0.
  by rewrite plane_axis_projection_value /coordinate_basis ffunE /j /= scale0r.
rewrite hom_compE hZero linear0 hom_of_linearE /= in hh.
have hCoord:=congr1 (fun x:R_n R 2=>x j) hh.
move/eqP:hCoord.
by rewrite /coordinate_basis !ffunE eqxx eq_sym oner_eq0.
Qed.

(** Federer (1969), 3.2.8, p. 247: regression
    for the project's zero-dimensional extension. Unit
    mass on R^0 makes an almost-everywhere conclusion
    true at its sole point. No punctured
    approximate differential is invoked in that dimension. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness LipschitzUP MeasureAlmostUP PointMassMeasure EuclideanLebesgueDimensions
  PartialFunctionUP NormDifferential LipschitzLeftInverseDifferentials.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [zero_dimensional_left_inverse_regression]:
    the empty-product boundary of Federer 3.2.8,
    p. 247, under the documented R^0 unit-mass
    convention. For arbitrary self-maps of R^0,
    both actual differential graphs at zero exist
    and their composition is the identity map. *)
Example zero_dimensional_left_inverse_regression (R:realType)
    (u v:inner_metric_space (@euclidean_inner_productP R 0)->
      inner_metric_space (@euclidean_inner_productP R 0)):
  exists L M:Hom (R_n R 0) (R_n R 0),
    partial_function_graph
      (norm_differential (inner_norm_real_norm (@euclidean_inner_productP R 0))
        (inner_norm_real_norm (@euclidean_inner_productP R 0)) setT u) 0 L /\
    partial_function_graph
      (norm_differential (inner_norm_real_norm (@euclidean_inner_productP R 0))
        (inner_norm_real_norm (@euclidean_inner_productP R 0)) setT v) (u 0) M /\
    hom_comp M L=hom_of_linear (linear_id (R_n R 0)).
Proof.
pose X:=inner_metric_space (@euclidean_inner_productP R 0).
have hLip (f:X->X):is_metric_lipschitz setT f.
  have he:f=(fun _:X=>0) by apply:funext=>x; exact:coordinate_zero.
  rewrite he; exists 1; split; first exact:ltr01.
  split; first exact:ler01.
  move=>x y _ _; rewrite mdistxx mul1r; exact:mdist_ge0.
have hNull:=federer_3_2_8 (hLip u) (hLip v).
apply:contrapT=>hNot.
have hBad:([set x:X|v (u x)=x] `\`
  [set a:X|exists L M:Hom (R_n R 0) (R_n R 0),
    partial_function_graph
      (norm_differential (inner_norm_real_norm (@euclidean_inner_productP R 0))
        (inner_norm_real_norm (@euclidean_inner_productP R 0)) setT u) a L /\
    partial_function_graph
      (norm_differential (inner_norm_real_norm (@euclidean_inner_productP R 0))
        (inner_norm_real_norm (@euclidean_inner_productP R 0)) setT v) (u a) M /\
    hom_comp M L=hom_of_linear (linear_id (R_n R 0))]) 0.
  split; first exact:coordinate_zero.
  exact hNot.
rewrite /measure_almost_everywhere_on /euclidean_lebesgue_measure in hNull.
rewrite (point_mass_in R hBad) in hNull.
have hOne:((1 : \bar R)<=0)%E by rewrite hNull; exact:lexx.
by rewrite lee_fin ler10 in hOne.
Qed.

(** Federer (1969), 3.2.9, p. 247: public
    interface regressions for the complementary-dimension
    and empty-locus boundaries. The scalar and
    Euclidean zero-dimensional conventions remain unchanged. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm
  HilbertFormCompactness NormDifferentialUP NormDifferentialLinear NormMetric CoordinateInverseCoverUP
  CoordinateInverseCover SurjectiveDifferentialDimension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [coordinate_cover_larger_target_regression]:
    the m<n boundary of Federer 3.2.9,
    p. 247. The public theorem accepts a
    continuous map R^0 to R^1, and its
    actual full-rank locus is empty. *)
Example coordinate_cover_larger_target_regression (R:realType):
  exists G,is_coordinate_inverse_cover (fun _:R_n R 0=>(0:R_n R 1)) G /\
    surjective_differential_locus (fun _:R_n R 0=>(0:R_n R 1))=set0.
Proof.
have hCont:continuous (fun _:real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R 0))=>
    (0:real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R 1)))).
  exact:cst_continuous.
have [G hG]:=federer_3_2_9 hCont.
exists G; split=>//.
exact:surjective_differential_locus_above_dimension_empty (isT : (0<1)%N).
Qed.

(** Source for [coordinate_cover_zero_point_regression]:
    both zero blocks in Federer 3.2.9,
    p. 247, under the project's unit-mass
    R^0 convention. The public cover actually
    contains the sole full-rank point; it cannot
    satisfy coverage by an empty family. *)
Example coordinate_cover_zero_point_regression (R:realType):
  exists G E,is_coordinate_inverse_cover (fun _:R_n R 0=>(0:R_n R 0)) G /\
    G E /\ E 0.
Proof.
pose X:=R_n R 0.
pose N:=inner_norm (@euclidean_inner_productP R 0).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R 0).
pose f:=fun _:X=>(0:X).
have hCont:continuous (fun _:real_norm_metric_space hN=>(0:real_norm_metric_space hN)).
  exact:cst_continuous.
have [G hG]:=federer_3_2_9 hCont.
have hFull:surjective_differential_locus f 0.
  exists (0:Hom X X); split.
  - apply:(norm_differential_constant hN hN).
    exists 1; split; first exact:ltr01; by move=>h hh.
  - move=>y; exists 0; rewrite linear0; exact:Logic.eq_sym (coordinate_zero y).
have [E hE hZero]:=hG.2.1 0 hFull.
exists G,E; by split=>//; split.
Qed.

(** Federer (1969), 3.2.10, p. 248: regressions for
    the complete coordinate-piece coarea theorem. Exercise the
    whole-space projection chart, a planar projection and the
    zero-dimensional target with its existing unit-mass convention. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates EuclideanBlockLinearMaps EuclideanRightBlockProjection EuclideanMetricProduct MetricCartesianProductUP
  CoordinateInverseCoverUP CoordinateCoarea EuclideanTargetJacobianMeasurable
  EuclideanLebesgueDimensions TopologicalBorel HausdorffMeasure MappingMultiplicity
  LipschitzUP MeasureUP MeasureIntegralUP MeasureSubsetIntegral PartialFunctionBasic ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [coordinate_projection_whole_piece_regression]:
    the projection instance of Federer 3.2.10, p. 248.
    Regression: the whole Euclidean space is an actual
    inverse coordinate piece of its first-block projection,
    including either empty block; no chart laws are postulated. *)
Example coordinate_projection_whole_piece_regression (R:realType) n k:
  is_coordinate_inverse_piece (@euclidean_first_block_map R n k) setT.
Proof.
rewrite /is_coordinate_inverse_piece addKn.
split; first exact (open_borel_set (@openT (inner_metric_space (@euclidean_inner_productP R (n+k))))).
exists (hom_as_linear (@euclidean_last_block_map R n k)); split.
- exact (@euclidean_right_block_orthogonal_projection R n k).
- pose X:=inner_metric_space (@euclidean_inner_productP R (n+k)).
  have hId:is_metric_lipschitz setT (fun x:X=>x).
    exists 1; split; first exact:ltr01.
    split; first exact:ler01; move=>x y _ _; by rewrite mul1r.
  exists (fun x:X=>x),(fun x:X=>x); split; first exact hId.
  split; first exact hId.
  move=>x _; split; last by [].
  exact (Logic.eq_sym (@euclidean_block_splitK R n k x)).
Qed.

(** Source for [planar_coordinate_coarea_regression]: Federer
    3.2.10, p. 248. Regression: the public theorem
    gives the actual J_1 integral and H^1 fibre integral
    for every measurable subset of the coordinate plane,
    using the proved whole-space inverse chart. *)
Example planar_coordinate_coarea_regression (R:realType)
    (B:set (R_n R 2)):
  measure_measurable (@euclidean_lebesgue_measure R 2) B ->
  exists a,is_measure_subset_integral (@euclidean_lebesgue_measure R 2) B
      (extended_euclidean_target_jacobian (@euclidean_first_block_map R 1 1)) a /\
    is_measure_integral (@euclidean_lebesgue_measure R 1)
      (partial_function_total (fun y=>(@hausdorff_measure R
        (inner_metric_space (@euclidean_inner_productP R 2)) 1
        (mapping_fibre (@euclidean_first_block_map R 1 1) B y):extended_real_line R))) a.
Proof.
move=>hB.
have hF:is_metric_lipschitz setT (fun x:inner_metric_space (@euclidean_inner_productP R 2)=>
      (@euclidean_first_block_map R 1 1 x:inner_metric_space (@euclidean_inner_productP R 1))).
  exists 1; split; first exact:ltr01.
  exact (metric_product_first_nonexpanding (@euclidean_blocks_are_metric_product R 1 1)).
exact (@federer_3_2_10 R 2 1 (@euclidean_first_block_map R 1 1) setT
  (erefl true) hF (coordinate_projection_whole_piece_regression R 1 1) B hB (subsetT B)).
Qed.

(** Source for [zero_target_coordinate_coarea_regression]:
    Federer 3.2.10, p. 248, with m=1,n=0.
    Regression: the public theorem retains degree-zero Jacobian
    normalization and the unit-mass target, for arbitrary
    measurable B, rather than imposing n>0. *)
Example zero_target_coordinate_coarea_regression (R:realType)
    (B:set (R_n R 1)):
  measure_measurable (@euclidean_lebesgue_measure R 1) B ->
  exists a,is_measure_subset_integral (@euclidean_lebesgue_measure R 1) B
      (extended_euclidean_target_jacobian (@euclidean_first_block_map R 0 1)) a /\
    is_measure_integral (@euclidean_lebesgue_measure R 0)
      (partial_function_total (fun y=>(@hausdorff_measure R
        (inner_metric_space (@euclidean_inner_productP R 1)) 1
        (mapping_fibre (@euclidean_first_block_map R 0 1) B y):extended_real_line R))) a.
Proof.
move=>hB.
have hF:is_metric_lipschitz setT (fun x:inner_metric_space (@euclidean_inner_productP R 1)=>
      (@euclidean_first_block_map R 0 1 x:inner_metric_space (@euclidean_inner_productP R 0))).
  exists 1; split; first exact:ltr01.
  exact (metric_product_first_nonexpanding (@euclidean_blocks_are_metric_product R 0 1)).
exact (@federer_3_2_10 R 1 0 (@euclidean_first_block_map R 0 1) setT
  (erefl true) hF (coordinate_projection_whole_piece_regression R 0 1) B hB (subsetT B)).
Qed.

(** Federer (1969), 3.2.11, p. 249: regressions
    for the complete coarea theorem. Exercise a genuinely
    critical map and the target dimension zero boundary. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  EuclideanLebesgueDimensions EuclideanLinearJacobian CoareaLinearDuality
  EuclideanCoareaFormula CriticalCoareaJacobianZero CoareaJacobianMeasure
  NormDifferentialUP NormDifferentialLinear LipschitzUP HausdorffMeasure MappingMultiplicity
  EuclideanTargetJacobianMeasurable EuclideanBlockLinearMaps EuclideanMetricProduct MetricCartesianProductUP
  MeasureUP MeasureIntegralUP MeasureSubsetIntegral PartialFunctionUP PartialFunctionBasic ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [constant_plane_coarea_regression]: the
    critical case of Federer 3.2.11, p. 249.
    For a constant map R^2 to R^1 the H^1
    fibre-mass integral is zero for every measurable A,
    although its fibre at the constant value can have infinite mass. *)
Example constant_plane_coarea_regression (R:realType) (c:R_n R 1) A:
  measure_measurable (@euclidean_lebesgue_measure R 2) A ->
  is_measure_integral (@euclidean_lebesgue_measure R 1)
    (partial_function_total (fun y=>(@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R 2)) 1
      (mapping_fibre (fun _:R_n R 2=>c) A y):extended_real_line R))) 0%E.
Proof.
move=>hA.
pose X:=inner_metric_space (@euclidean_inner_productP R 2).
pose Y:=inner_metric_space (@euclidean_inner_productP R 1).
pose f:=fun _:X=>(c:Y).
have hf:is_metric_lipschitz setT f.
  exists 1; split; first exact:ltr01.
  split; first exact:ler01; move=>x y _ _; rewrite mdistxx mul1r; exact:mdist_ge0.
have hJ:euclidean_linear_jacobian 1 (0:Hom (R_n R 2) (R_n R 1))=0.
  have hNonnegative:=euclidean_linear_jacobian_nonnegative 1 (0:Hom (R_n R 2) (R_n R 1)).
  case:(ltP 0 (euclidean_linear_jacobian 1 (0:Hom (R_n R 2) (R_n R 1))))=>[hp|hle].
  - have hRank:=(euclidean_target_jacobian_positive_iff_surjective (0:Hom (R_n R 2) (R_n R 1))).1 hp.
    have [x hx]:=hRank [ffun _:'I_1=>(1:R)].
    have hBad:=congr1 (fun y:R_n R 1=>y ord0) hx.
    rewrite hom_zeroE !ffunE in hBad.
    have hNe:=oner_neq0 R; by rewrite -hBad eqxx in hNe.
  - by apply/eqP; rewrite eq_le hle hNonnegative.
have hZero:euclidean_coarea_measure f A=0%E.
  apply:critical_coarea_jacobian_measure_zero=>x hx.
  exists (0:Hom (R_n R 2) (R_n R 1)); split; last exact hJ.
  apply:(norm_differential_constant
    (inner_norm_real_norm (@euclidean_inner_productP R 2))
    (inner_norm_real_norm (@euclidean_inner_productP R 1))).
  exists 1; split; first exact:ltr01; by move=>h hh.
have hI:=euclidean_coarea_formula (isT:(1<2)%N) hf hA.
by rewrite hZero in hI.
Qed.

(** Source for [zero_target_global_coarea_regression]:
    Federer 3.2.11, p. 249 with m=1,n=0.
    The complete public theorem retains the actual partial
    Jacobian domain and unit-mass R^0 without a coordinate-chart premise. *)
Example zero_target_global_coarea_regression (R:realType) (A:set (R_n R 1)):
  measure_measurable (@euclidean_lebesgue_measure R 1) A ->
  exists a,is_measure_subset_integral (@euclidean_lebesgue_measure R 1) A
      (extended_euclidean_target_jacobian (@euclidean_first_block_map R 0 1)) a /\
    is_measure_integral (@euclidean_lebesgue_measure R 0)
      (partial_function_total (fun y=>(@hausdorff_measure R
        (inner_metric_space (@euclidean_inner_productP R 1)) 1
        (mapping_fibre (@euclidean_first_block_map R 0 1) A y):extended_real_line R))) a.
Proof.
move=>hA.
have hf:is_metric_lipschitz setT (fun x:inner_metric_space (@euclidean_inner_productP R 1)=>
    (@euclidean_first_block_map R 0 1 x:inner_metric_space (@euclidean_inner_productP R 0))).
  exists 1; split; first exact:ltr01.
  exact (metric_product_first_nonexpanding (@euclidean_blocks_are_metric_product R 0 1)).
exact (@federer_3_2_11 R 1 0 (@euclidean_first_block_map R 0 1) A (erefl true) hf hA).
Qed.

(** Federer (1969), 3.2.12, pp. 249–250: regressions
    for zero weight on infinite sources and negative weights
    without a source summability restriction. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanWeightedCoarea CoareaFibreIntegral EuclideanTargetJacobianMeasurable LipschitzUP
  PartialFunctionUP PartialFunctionBasic PartialDensityProduct SummableRealFunctionUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasureIntegralUP
  MeasureIntegralGraphEquivalence MeasureIntegralUniqueness MeasureIntegralAlmostEquality
  MeasureIntegralNegationLaw MeasureConullZeroIntegral MeasureExtendedCharacteristicIntegral
  CharacteristicFunctionUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [zero_weight_global_coarea_regression]:
    Federer 3.2.12, pp. 249–250 with g=0.
    No finite source mass is needed, and the actual
    partial Jacobian domain is preserved in the source integral. *)
Example zero_weight_global_coarea_regression (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)):
  (n<m)%N ->is_metric_lipschitz setT f ->
  is_measure_integral (@euclidean_lebesgue_measure R n)
    (coarea_fibre_integral f (real_total_integrand (fun _:R_n R m=>(0:R)))) 0%E.
Proof.
move=>hnm hf.
pose mu:=@euclidean_lebesgue_measure R m.
pose hm:=euclidean_lebesgue_is_measure R m.
pose u:=real_total_integrand (fun _:R_n R m=>(0:R)).
have hZero:is_measure_integral mu u 0%E.
  apply:(measure_almost_zero_integral hm).
  apply:(@measure_almost_everywhere_mono R _ mu hm setT _ _ (measure_almost_everywhere_true hm))=>x _.
  by apply/real_total_integrand_graph.
have hJac:=extended_euclidean_target_jacobian_measurable hf.
have hProduct:is_measure_integral mu (partial_density_product u (extended_euclidean_target_jacobian f)) 0%E.
  apply:(measure_almost_zero_integral hm).
  apply:(@measure_almost_everywhere_mono R _ mu hm _ _ _ (measurable_function_domain hJac))=>x [j hj].
  apply/partial_density_product_graph; exists 0%E,j; split; first by apply/real_total_integrand_graph.
  by split=> //; rewrite mul0e.
have [a [hLeft hRight]]:=federer_3_2_12 hnm hf (ex_intro _ 0%E hZero).
have hEq:=measure_integral_unique hLeft hProduct.
by rewrite hEq in hRight.
Qed.

(** Source for [negative_characteristic_coarea_regression]:
    Federer 3.2.12, pp. 249–250 accepts g=-chi_A
    even when A has infinite measure. The source integral
    of g is -mu(A), so this tests integrability rather
    than an inadvertently stronger summability premise. *)
Example negative_characteristic_coarea_regression (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) A (chi:R_n R m->R):
  (n<m)%N ->is_metric_lipschitz setT f ->
  measure_measurable (@euclidean_lebesgue_measure R m) A ->is_characteristic_function A chi ->
  exists a,is_measure_integral (@euclidean_lebesgue_measure R m)
      (partial_density_product (real_total_integrand (fun x=>-chi x)) (extended_euclidean_target_jacobian f)) a /\
    is_measure_integral (@euclidean_lebesgue_measure R n)
      (coarea_fibre_integral f (real_total_integrand (fun x=>-chi x))) a.
Proof.
move=>hnm hf hA hChi.
pose mu:=@euclidean_lebesgue_measure R m.
pose hm:=euclidean_lebesgue_is_measure R m.
have hPos:=measure_total_characteristic_integral hm hChi hA.
have hNeg:=measure_integral_negation hm hPos.
have hWeight:is_measure_integral mu (real_total_integrand (fun x=>-chi x)) (-mu A)%E.
  apply:(measure_integral_graph_equivalent _ hNeg)=>x j.
  split.
  - move=>[v [hv <-]]; apply/real_total_integrand_graph; by rewrite EFinN -(hv:(chi x)%:E=v).
  - move/real_total_integrand_graph=>hj; exists (chi x)%:E; split; first by [].
    by rewrite -hj EFinN.
exact (federer_3_2_12 hnm hf (ex_intro _ (-mu A)%E hWeight)).
Qed.

From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import EulerGamma EulerGammaHalfParameters EulerGammaGaussian GammaSquareIntegrand
  RealPower RealExponentialUP RealExponentialSealed UnitSphereSpace UnitSphereCoordinatePower
  SphereCoordinateParameters SphereCoordinateMoment ProjectionBeta ProjectionBetaGammaProduct ProjectionBetaFirstGamma
  GammaHalfSequences PartialFunctionUP MeasureIntegralUP SummableRealFunctionUP.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Close Scope ereal_scope.

(** Source for [gamma_half_nonzero_origin_regression]: the
    square-substitution formula of Federer 3.2.13, p. 250,
    keeps the printed integrand at the critical zero exponent:
    its origin value is one, not the auxiliary zero completion. *)
Example gamma_half_nonzero_origin_regression (R:realType):
  gamma_square_integrand (1/2:R) 0= 1 /\
  is_measure_integral (@LebesgueScalarMeasure.lebesgue_scalar_measure R)
    (real_total_integrand (gamma_square_integrand (1/2:R))) (euler_gamma_half R)%:E.
Proof.
split; last exact:euler_gamma_gaussian_integral (positive_real_half R).
have hTwo:(2:R)!= 0 by apply/eqP; lra.
have hExponent:2*(1/2:R)-1= 0 by rewrite div1r mulfV // subrr.
by rewrite /gamma_square_integrand expr0n /= oppr0 normr0 hExponent
  (real_exponential_zero (@RealExponential.laws R)) real_power_zero_exponent mul1r.
Qed.

(** Source for [sphere_line_negative_moment_regression]: the
    full t>-1 range of the coordinate moment in Federer 3.2.13,
    p. 251, includes a negative exponent on the two-point
    sphere S^0; its actual integral is two. *)
Example sphere_line_negative_moment_regression (R:realType):
  is_measure_integral (@unit_sphere_hausdorff_measure R 1)
    (real_total_integrand (unit_sphere_coordinate_power ord0 (-1/2:R))) (2%R)%:E.
Proof.
have ht:(-1:R)< -1/2 by lra.
have hI:=@unit_sphere_coordinate_power_integral R 1 (ltn0Sn 0%N) ord0 (-1/2:R) ht.
have hDen:euler_gamma (@positive_coordinate_moment_denominator R 1 (-1/2:R) (ltn0Sn 0%N) ht)=
    euler_gamma (positive_coordinate_moment_parameter ht).
  exact:euler_gamma_proof_irrelevant.
have hValue:2*euler_gamma (positive_coordinate_moment_parameter ht)*(euler_gamma_half R)^+(1-1)/
    euler_gamma (@positive_coordinate_moment_denominator R 1 (-1/2:R) (ltn0Sn 0%N) ht)= 2.
  rewrite hDen subnn expr0 mulr1 mulfK //.
  exact:lt0r_neq0 (euler_gamma_positive (positive_coordinate_moment_parameter ht)).
by rewrite hValue in hI.
Qed.

(** Source for [beta_gamma_empty_product_regression]: the n=m
    case of the product in Federer 3.2.13, p. 251,
    is the empty product one, including every finite t>= 1. *)
Example beta_gamma_empty_product_regression (R:realType) m (hm:(0<m)%N) (t:R) (ht:1<=t):
  real_power (@projection_beta R m m (leqnn m) t%:E) t= 1.
Proof.
have h:=@projection_beta_gamma_product R m m hm (leqnn m) t ht.
by rewrite subnn big_ord0 in h.
Qed.

(** Source for [beta_first_complementary_degrees_regression]:
    the final Gamma quotient in Federer 3.2.13, p. 251,
    is symmetric in the positive complementary degrees m and n-m. *)
Example beta_first_complementary_degrees_regression (R:realType) n m (hm:(0<m)%N)
    (hmn:(m<n)%N) (hc:(0<n-m)%N):
  @projection_beta R n m (ltnW hmn) (1%R:R)%:E=
    @projection_beta R n (n-m) (leq_subr m n) (1%R:R)%:E.
Proof.
rewrite (@projection_beta_first_gamma_formula R n m hm (ltnW hmn))
  (@projection_beta_first_gamma_formula R n (n-m) hc (leq_subr m n))
  (subKn (ltnW hmn)).
by rewrite (mulrC (gamma_half_sequence R m) (gamma_half_sequence R (n-m))).
Qed.

(** Boundary regressions for Federer (1969), 3.2.14,
    pp. 251–252. The finite-set convention in dimension
    zero is essential and differs from images of R^0. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  PartialFunctionUP PartialMetricLipschitz RealMetricBackground
  RectifiableSetUP RectifiableElementary RectifiableZeroDimension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [zero_rectifiable_pair_regression]: the
    finite-set convention of Federer 3.2.14, p. 252,
    includes the two distinct points zero and one. *)
Lemma zero_rectifiable_pair_regression (R : realType) :
  @is_m_rectifiable R (real_line_metric R) 0 [set 0;1].
Proof. exact: finite_set2. Qed.

(** Source for [zero_parameter_pair_impossible_regression]:
    the necessity of Federer's replacement convention,
    3.2.14, p. 252. A partial map from R^0 cannot
    have both zero and one in its image. *)
Lemma zero_parameter_pair_impossible_regression (R : realType)
    (f : partial_function (inner_metric_space (@euclidean_inner_productP R 0)) (real_line_metric R)) :
  partial_function_range f<>[set 0;1].
Proof.
move=> hr.
have h0 : partial_function_range f 0 by rewrite hr; left.
have h1 : partial_function_range f 1 by rewrite hr; right.
have [x hx] := h0; have [y hy] := h1.
have hxy : x=y.
  apply/ffunP=> i; by have := ltn_ord i; rewrite ltn0.
rewrite -hxy in hy.
have he : (0 : R)= 1 := partial_function_single_valued hx hy.
by have := oner_neq0 R; rewrite -he eqxx.
Qed.

(** Source for [countably_zero_natural_image_regression]:
    countably zero rectifiable includes a countable
    Euclidean-line image, by the final convention of
    Federer 3.2.14, p. 252. *)
Lemma countably_zero_natural_image_regression (R : realType) :
  @is_countably_m_rectifiable R (real_line_metric R) 0
    ((fun n : nat => (n%:R : real_line_metric R)) @` setT).
Proof.
apply: (proj2 (@countably_zero_rectifiable_countable R (real_line_metric R) _)).
exact: sub_countable (card_image_le _ _) (countableP setT).
Qed.

(** Federer (1969), 3.2.15, p. 252: the
    zero-dimensional target is part of the printed
    m>n theorem. These regressions retain that case. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  LipschitzUP LipschitzBasic RectifiableSetUP EuclideanLipschitzRectifiableImage
  LipschitzFibreRectifiability EuclideanLebesgueDimensions HausdorffMeasure
  MappingMultiplicity MeasureAlmostUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [zero_target_whole_fibre_regression]:
    the full-rank parametrization boundary of Federer
    3.2.15, p. 252. The unique fibre of the
    constant map to R^0 is countably m rectifiable. *)
Example zero_target_whole_fibre_regression (R : realType) m :
  @is_countably_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R m)) m
    (mapping_fibre (fun _ : inner_metric_space (@euclidean_inner_productP R m) =>
      (0 : inner_metric_space (@euclidean_inner_productP R 0))) setT 0).
Proof.
pose X := inner_metric_space (@euclidean_inner_productP R m).
have he : mapping_fibre (fun _ : X =>
    (0 : inner_metric_space (@euclidean_inner_productP R 0))) setT 0=
    (fun x : X => x) @` setT.
  apply/seteqP; split=> x.
  - move=> hx; by exists x.
  - move=> [y _ <-]; by split.
rewrite he; apply: euclidean_lipschitz_image_countably_rectifiable.
exists 1; split; first exact: ltr01.
split; first exact: ler01.
by move=> x y hx hy; rewrite mul1r.
Qed.

(** Source for [zero_target_almost_rectifiable_regression]:
    the zero-target specialization of the actual
    conclusion of Federer 3.2.15, p. 252. No
    n>0 premise is inserted into the coarea reduction. *)
Example zero_target_almost_rectifiable_regression (R : realType) m :
  (0<m)%N ->
  measure_almost_everywhere (@euclidean_lebesgue_measure R 0)
    [set y | @is_countably_measure_m_rectifiable R
      (inner_metric_space (@euclidean_inner_productP R m))
      (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) m)
      m (mapping_fibre (fun _ : inner_metric_space (@euclidean_inner_productP R m) =>
        (0 : inner_metric_space (@euclidean_inner_productP R 0))) setT y)].
Proof.
move=> hm.
pose f := fun _ : inner_metric_space (@euclidean_inner_productP R m) =>
  (0 : inner_metric_space (@euclidean_inner_productP R 0)).
have hf : is_metric_lipschitz setT f.
  apply: (@metric_lipschitz_of_bound R
    (inner_metric_space (@euclidean_inner_productP R m))
    (inner_metric_space (@euclidean_inner_productP R 0)) setT f 0).
  split; first exact: lexx.
  by move=> x y hx hy; rewrite /f mdistxx mul0r.
have hh := @federer_3_2_15 R m 0 f hm hf.
by rewrite subn0 in hh.
Qed.

(** Federer (1969), 3.2.16, pp. 252–254:
    public regressions for missing null base
    points, the empty-measure closure boundary and
    the exact domain of the opaque differential. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm RealNormUP NormMetric HilbertFormCompactness EuclideanLebesgueDimensions
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  MeasureUP ApproximateDifferentialUP ApproximateDifferentialAffine
  MeasureApproximateDifferentialUP MeasureApproximateDifferential
  MeasureApproximateBoundary MeasureApproximateNullBasePoint.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [punctured_euclidean_approximation_regression]:
    the corrected generalization in Federer
    3.2.16, p. 254 line 2. A constant
    map with its null base point removed
    satisfies the new definition and fails the
    older actual-domain premise in 3.1.2. *)
Example punctured_euclidean_approximation_regression (R : realType) n
    (a : R_n R n.+1) (eta : R) :
  has_measure_approximate_differential (fun y : R^o=> `|y|)
    (inner_norm_real_norm (@euclidean_inner_productP R n.+1))
    (@euclidean_lebesgue_measure R n.+1) n.+1
    (partial_function_source_restrict (~` [set a])
      (partial_function_total (fun _ : R_n R n.+1=>eta))) a 0 /\
  ~has_approximate_differential (fun y : R^o=> `|y|) (~` [set a])
    (fun _ : R_n R n.+1=>eta) a 0.
Proof.
split.
- exact: (@measure_approximate_punctured_constant R (R_n R n.+1) R^o
    (inner_norm (@euclidean_inner_productP R n.+1)) (fun y : R^o=> `|y|)
    (inner_norm_real_norm (@euclidean_inner_productP R n.+1))
    (@scalar_absolute_value_norm R) (@euclidean_lebesgue_measure R n.+1) n.+1 a eta
    (euclidean_lebesgue_is_measure R n.+1) (positive_euclidean_singleton_null a)).
- by move=> [hne _]; apply: hne.
Qed.

(** Source for [empty_approximation_closure_regression]:
    the agreement-set assertion in Federer
    3.2.16, p. 253, read with the
    closure domain of 3.1.22, p. 235.
    Approximate differentiability alone does not
    force that closure at a zero measure. *)
Example empty_approximation_closure_regression (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY) m
    (a : X) (U : set X) (g : X -> Y) :
  measure_approximately_differentiable_at NY hNX (fun _=>0%E) m
    (@partial_function_empty X Y) a /\
  ~@closure (real_norm_metric_space hNX)
    (partial_function_agreement (@partial_function_empty X Y)
      (partial_function_source_restrict U (partial_function_total g))) a.
Proof.
split.
- exact: (@measure_approximate_empty_zero R X Y NX NY hNX hNY m a).
- exact: measure_approximate_empty_agreement_not_closure.
Qed.

(** Source for [empty_approximate_differential_domain_regression]:
    the exact cone-domain convention for ap Df,
    Federer 3.2.16, p. 253. At a zero
    measure the opaque differential is defined
    as a partial function with empty domain,
    rather than an arbitrary ambient zero map. *)
Example empty_approximate_differential_domain_regression (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY) m (a : X) :
  partial_function_domain (@measure_approximate_differential R X Y NX NY hNX hNY
    (fun _=>0%E) m (measure_approximate_zero_measure_law R X)
    (@partial_function_empty X Y) a
    (@measure_approximate_empty_zero R X Y NX NY hNX hNY m a))=set0.
Proof.
rewrite measure_approximate_differential_domain.
exact: measure_approximate_zero_tangent_empty.
Qed.

(** Federer (1969), 3.2.17, pp. 254–255:
    the zero-dimensional parameter space gives
    a single image point. Retain unit density
    and relative differentiability for every ambient
    map, without an off-image regularity premise. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm InnerMetric RealNormUP HilbertFormCompactness
  NormDifferentialUP NormOpenDomainLaws NormDifferentialLinear
  PartialFunctionUP PartialFunctionBasic PartialFunctionPrecomposition
  MeasureUP MeasureBasic MeasureRestriction MetricClosedBalls
  EuclideanLebesgueDimensions EuclideanClosedBallVolume EuclideanNoncenteredVitali
  CenteredBallRelations CenteredNullSetDensity MeasureSetDensity
  MetricDensities MetricBiLipschitzUP HausdorffMeasure RelativeDifferentialUP
  EuclideanParametrizedDensityTangent EuclideanBiLipschitzRelativeComposite.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section PointImage.
Variable R : realType.
Variable n : nat.
Variable b : R_n R n.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R 0)).
Local Notation Y := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 0)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R 0)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).

(** Source for [point_parameter_bilipschitz]: supporting
    the dimension-zero specialization of Federer
    3.2.17, p. 254. The zero-dimensional
    source contains exactly one point. *)
Local Lemma point_parameter_bilipschitz :
  @is_metric_bilipschitz_bound R X Y setT (fun _=>b) 2.
Proof.
split.
- split; first by rewrite ler0n.
  move=> x y _ _.
  change (is_true (mdist (b:Y) b<=2*mdist x y)).
  have h2 : 0<=(2:R) by rewrite ler0n.
  rewrite mdistxx; exact: (mulr_ge0 h2 (mdist_ge0 x y)).
- move=> x y _ _.
  have heq : x=y by rewrite (@coordinate_zero R x) (@coordinate_zero R y).
  by rewrite heq !mdistxx mulr0.
Qed.

(** Source for [point_parameter_full_density]: the
    full-domain density hypothesis in Federer
    3.2.17, p. 254, specialized to
    the complete zero-dimensional parameter space. *)
Local Lemma point_parameter_full_density :
  partial_function_graph (measure_set_density (@euclidean_lebesgue_measure R 0)
    (@centered_closed_ball_relation R [the metricType R of X]) (~` setT)) (0:X) 0%E.
Proof.
apply: (@centered_null_set_density_zero R X (@euclidean_lebesgue_measure R 0)
  (~` setT) 0 (euclidean_lebesgue_is_measure R 0) _ _).
- move=> x r hr; split; first exact: euclidean_closed_ball_positive.
  by rewrite (euclidean_closed_ball_normalized_volume x (ltW hr)) fin_numE.
- have heq : (~` (@setT X))=set0.
    apply/seteqP; split=> x; [by move=> hn; apply: hn|by move=> []].
  by rewrite heq (measure_empty (euclidean_lebesgue_is_measure R 0)).
Qed.

(** Source for [point_parameter_linear_injective]: the
    univalent differential in the zero-source
    case of Federer 3.2.17, p. 254.
    Its range is the zero tangent plane. *)
Local Lemma point_parameter_linear_injective : injective (0 : Hom (R_n R 0) (R_n R n)).
Proof. by move=> x y _; rewrite (@coordinate_zero R x) (@coordinate_zero R y). Qed.

(** Source for [zero_source_parametrized_density_regression]:
    both density bounds in Federer 3.2.17,
    p. 254, equal one when m=0.
    The resulting common metric density is
    exactly one, in every ambient dimension. *)
Example zero_source_parametrized_density_regression :
  partial_function_graph (metric_density 0 (measure_restrict
    (@hausdorff_measure R Y 0) ((fun _ : X=>b) @` setT))) b 1%E.
Proof.
have hPsi := @norm_differential_constant R (R_n R 0) (R_n R n) NX NY hNX hNY
  setT 0 b (@norm_full_domain_interior R (R_n R 0) NX 0).
have h2 : 1<(2:R) by rewrite ltr1n.
have hMain := @federer_3_2_17 R 0 n setT (fun _=>b) 2 0 0
  point_parameter_bilipschitz h2 I point_parameter_linear_injective hPsi point_parameter_full_density.
have [hLower [hOrder [hUpper _]]] := hMain.
rewrite addn0 expr0 invr1 in hLower.
rewrite addn0 expr0 in hUpper.
split; apply/eqP; rewrite eq_le; apply/andP; split=> //.
- exact: le_trans hLower hOrder.
- exact: le_trans hOrder hUpper.
Qed.

(** Source for [zero_source_relative_composite_regression]:
    the "Moreover" conclusion of Federer
    3.2.17, pp. 254–255. Any ambient
    F is differentiable relative to the
    point image; no regularity off that
    point is needed. Its composite derivative
    on the zero source is exactly zero. *)
Example zero_source_relative_composite_regression k (F : R_n R n -> R_n R k) :
  exists d : partial_function (R_n R n) (R_n R k),
    @has_relative_norm_differential R (R_n R n) (R_n R k) NY
      (inner_norm (@euclidean_inner_productP R k)) hNY
      setT ((fun _ : X=>b) @` setT) F b d /\
    partial_function_precompose (0 : Hom (R_n R 0) (R_n R n)) d=
      partial_function_total (0 : Hom (R_n R 0) (R_n R k)).
Proof.
have hPsi := @norm_differential_constant R (R_n R 0) (R_n R n) NX NY hNX hNY
  setT 0 b (@norm_full_domain_interior R (R_n R 0) NX 0).
have hComp := @norm_differential_constant R (R_n R 0) (R_n R k) NX
  (inner_norm (@euclidean_inner_productP R k)) hNX
  (inner_norm_real_norm (@euclidean_inner_productP R k)) setT 0 (F b)
  (@norm_full_domain_interior R (R_n R 0) NX 0).
apply: (@euclidean_bilipschitz_relative_composite R 0 n (R_n R k)
  (inner_norm (@euclidean_inner_productP R k))
  (inner_norm_real_norm (@euclidean_inner_productP R k)) setT (fun _=>b) F 2 0 0 0
  point_parameter_bilipschitz _ I point_parameter_linear_injective hPsi hComp point_parameter_full_density).
by rewrite ltr0n.
Qed.
End PointImage.

(** Federer 3.2.18, p. 255: public whole-theorem regressions
    for the empty set and the zero-dimensional point boundary. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  MeasureUP MeasureBasic MeasureFiniteClosure MeasureAlmostUP MeasureAlmostBasic
  RectifiableSetUP RectifiableElementary RectifiableCompactChartsUP RectifiableCompactCharts
  HausdorffMeasure HausdorffCountingMeasure HausdorffClosedCoverAgreement
  BorelRegularMeasureUP FiniteExceptionalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [empty_rectifiable_compact_chart_cover_regression]:
    empty W in the complete conclusion of Federer 3.2.18, p. 255.
    The actual theorem supplies a sequence in every pair of natural
    dimensions; no inhabited parameter image is required. *)
Example empty_rectifiable_compact_chart_cover_regression (R : realType) m n :
  exists (K : nat -> set (R_n R m)) (psi : nat -> R_n R m -> R_n R n),
    is_rectifiable_compact_chart_cover (2:R) set0 K psi.
Proof.
pose Y := inner_metric_space (@euclidean_inner_productP R n).
pose mu := @hausdorff_measure R Y m.
have hm := @hausdorff_measure_is_measure R Y m.
have hCount : is_countably_measure_m_rectifiable mu m set0.
  split=> //; exists set0; split; first exact: countably_rectifiable_empty.
  rewrite /measure_almost_included setDv; exact: measure_empty hm.
have hFin : (mu set0< +oo)%E by rewrite /mu (measure_empty hm); exact: lt0y.
apply: (@federer_3_2_18 R m n 2 set0 (conj hCount hFin) (measure_null_measurable hm (measure_empty hm))).
by rewrite ltr1n.
Qed.

(** Source for [point_rectifiable_compact_chart_cover_regression]:
    the finite-set convention of 3.2.14, p. 252, in the complete
    chart theorem 3.2.18, p. 255. A point of R^n has H^0 mass
    one, so its chart covering cannot be discharged by a null-set
    premise; the actual global maps and pointwise differential laws
    are supplied by the whole theorem. *)
Example point_rectifiable_compact_chart_cover_regression (R : realType) n (b : R_n R n) :
  exists (K : nat -> set (R_n R 0)) (psi : nat -> R_n R 0 -> R_n R n),
    is_rectifiable_compact_chart_cover (2:R) [set b] K psi.
Proof.
pose Y := inner_metric_space (@euclidean_inner_productP R n).
pose mu := @hausdorff_measure R Y 0.
have hm := @hausdorff_measure_is_measure R Y 0.
have hCount : is_countably_measure_m_rectifiable mu 0 [set b].
  split=> //; exists [set b]; split.
  - exact: (@rectifiable_countably_rectifiable R Y 0 [set b] (@finite_set1 Y b)).
  - rewrite /measure_almost_included setDv; exact: measure_empty hm.
have hFin : (mu [set b]< +oo)%E by rewrite /mu hausdorff_zero_singleton; exact: ltry.
have hMeas : measure_measurable mu [set b].
  exact: (@borel_regular_borel_measurable R Y mu hm (@hausdorff_measure_borel_regular R Y 0)
    [set b] (@finite_metric_set_borel R [the metricType R of Y] [set b] (@finite_set1 Y b))).
apply: (@federer_3_2_18 R 0 n 2 [set b] (conj hCount hFin) hMeas).
by rewrite ltr1n.
Qed.

(** Federer 3.2.19, p. 256: zero-dimensional positive-atom
    regressions for density, tangent dimension and the exact partial
    domain of the approximate differential. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  PartialMetricLipschitz RectifiableSetUP RectifiableElementary RectifiableTangentPlaneUP
  RectifiableDensityTangent MeasureApproximateTangentUP MeasureApproximateDifferentialUP
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasureRestriction
  HausdorffMeasure HausdorffCountingMeasure HausdorffClosedCoverAgreement
  BorelRegularMeasureUP FiniteExceptionalBorel MetricDensities.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section PointRectifiableDensity.
Variable R : realType.
Variable n : nat.
Variable b : R_n R n.
Local Notation Y := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation mu := (@hausdorff_measure R Y 0).

(** Source for [point_hausdorff_almost_property]: supporting positive-atom
    test for Federer 3.2.19, p. 256. Since H^0{b}=1 by
    2.10.2(1), p. 171, an almost-everywhere assertion on that singleton
    must hold at b itself; these regressions are not vacuous null-set tests. *)
Local Lemma point_hausdorff_almost_property (P : set (R_n R n)) :
  measure_almost_everywhere_on mu [set b] P -> P b.
Proof.
move=> hAE; apply: contrapT=> hn.
have hNull : mu [set b]=0%E.
  apply: (measure_null_subset (@hausdorff_measure_is_measure R Y 0) _ hAE).
  by move=> x ->; split.
have hPos : (0<mu [set b])%E by rewrite hausdorff_zero_singleton lte_fin ltr01.
by rewrite hNull ltxx in hPos.
Qed.

(** Source for [point_hausdorff_rectifiable]: the finite-set convention
    in Federer 3.2.14, p. 252, used to check the positive
    dimension-zero boundary of 3.2.19, p. 256. *)
Local Lemma point_hausdorff_rectifiable : is_measure_m_rectifiable mu 0 [set b].
Proof.
have hm := @hausdorff_measure_is_measure R Y 0.
split; last by rewrite hausdorff_zero_singleton; exact: ltry.
split; first exact hm.
exists [set b]; split.
- exact: (@rectifiable_countably_rectifiable R Y 0 [set b] (@finite_set1 Y b)).
- rewrite /measure_almost_included setDv; exact: measure_empty hm.
Qed.

(** Source for [point_hausdorff_measurable]: singleton measurability
    required in the whole-theorem regression for Federer 3.2.19,
    p. 256. It follows from metric Borel regularity, independently
    of the theorem being tested. *)
Local Lemma point_hausdorff_measurable : measure_measurable mu [set b].
Proof.
exact: (@borel_regular_borel_measurable R Y mu (@hausdorff_measure_is_measure R Y 0)
  (@hausdorff_measure_borel_regular R Y 0) [set b]
  (@finite_metric_set_borel R [the metricType R of Y] [set b] (@finite_set1 Y b))).
Qed.

(** Source for [zero_dimensional_rectifiable_density_tangent_regression]:
    the first assertion of Federer 3.2.19, p. 256, applied to
    an H^0 positive-mass point in arbitrary ambient dimension. The
    actual density equals one and the approximate tangent has dimension zero. *)
Example zero_dimensional_rectifiable_density_tangent_regression :
  partial_function_graph (metric_density 0 (measure_restrict mu [set b])) b 1%E /\
  is_m_dimensional_approximate_tangent 0 (measure_restrict mu [set b]) b.
Proof.
have hAE := (@federer_3_2_19 R 0 n [set b] point_hausdorff_rectifiable point_hausdorff_measurable).1.
exact: (point_hausdorff_almost_property hAE).
Qed.

(** Source for [point_partial_approximate_differential_regression]: the
    second assertion and displayed partial domain in Federer 3.2.19,
    p. 256, for a map defined only on an H^0 positive-mass
    point. The actual whole theorem yields an approximate differential
    there, with exactly its approximate tangent domain. *)
Example point_partial_approximate_differential_regression k (c : R_n R k) :
  exists d : partial_function (R_n R n) (R_n R k),
    is_measure_approximate_differential (inner_norm (@euclidean_inner_productP R k))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) (measure_restrict mu [set b]) 0
      (partial_function_source_restrict [set b] (partial_function_total (fun _=>c))) b d /\
    partial_function_domain d=measure_approximate_tangent_cone
      (inner_norm_real_norm (@euclidean_inner_productP R n)) (measure_restrict mu [set b]) 0 b.
Proof.
pose f := partial_function_source_restrict [set b] (partial_function_total (fun _ : R_n R n=>c)).
have hDom : partial_function_domain f=[set b].
  apply/seteqP; split; first by move=> x [y [hx _]].
  move=> x hx; exists c; by split.
have hLip : @is_partial_metric_lipschitz_bound R [the metricType R of Y]
    (inner_metric_space (@euclidean_inner_productP R k)) f 0.
  split; first exact: lexx.
  by move=> x y u v [_ <-] [_ <-]; rewrite mdistxx mul0r.
have hAE := (@federer_3_2_19 R 0 n [set b] point_hausdorff_rectifiable point_hausdorff_measurable).2
  k f hDom (ex_intro _ 0 hLip).
exact: (point_hausdorff_almost_property hAE).
Qed.
End PointRectifiableDensity.

(** Federer 3.2.20, pp. 256–257: positive-atom
    regressions for the actual partial domain, degree-zero Jacobian,
    and both infinite signed integral values. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialFunctionPostcomposition
  PartialMetricLipschitz RectifiableSetUP RectifiableElementary RectifiableDensityTangent
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasureRestriction MeasurableFunctionUP
  HausdorffMeasure HausdorffCountingMeasure HausdorffClosedCoverAgreement BorelRegularMeasureUP FiniteExceptionalBorel
  CountingMeasure CountingInjectionBound CharacteristicFunctionUP CharacteristicFunctionSealed
  MeasureIntegralUP MeasureIntegralNegationLaw MeasureIntegralNegation MeasureIntegralGraphEquivalence
  MeasureExtendedCharacteristicIntegral ExtendedRealOrderTopology
  MeasureApproximateTangentUP MeasureApproximateDifferentialUP MeasureApproximateJacobian PartialMappingMultiplicity RectifiableAreaIntegrands RectifiableAreaFormula.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section PointRectifiableArea.
Variable R : realType.
Variables n k : nat.
Variable b : R_n R n.
Variable c : R_n R k.
Local Notation Y := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation Z := (inner_metric_space (@euclidean_inner_productP R k)).
Local Notation mu := (@hausdorff_measure R Y 0).
Local Notation nu := (@hausdorff_measure R Z 0).
Local Notation f := (partial_function_source_restrict [set b]
  (partial_function_total (fun _ : R_n R n=>c))).

(** Source for [area_point_rectifiable]: finite-set case of 3.2.14,
    p. 252, supporting a positive-mass test of 3.2.20,
    p. 256. The source singleton has H^0 mass one. *)
Local Lemma area_point_rectifiable : is_measure_m_rectifiable mu 0 [set b].
Proof.
have hm := @hausdorff_measure_is_measure R Y 0.
split; last by rewrite hausdorff_zero_singleton; exact: ltry.
split; first exact hm.
exists [set b]; split.
- exact: (@rectifiable_countably_rectifiable R Y 0 [set b] (@finite_set1 Y b)).
- rewrite /measure_almost_included setDv; exact: measure_empty hm.
Qed.

(** Source for [area_point_measurable]: singleton measurability
    from 2.10.2(1), p. 171, for the 3.2.20, p. 256,
    positive-atom regression. *)
Local Lemma area_point_measurable : measure_measurable mu [set b].
Proof.
exact: (@borel_regular_borel_measurable R Y mu (@hausdorff_measure_is_measure R Y 0)
  (@hausdorff_measure_borel_regular R Y 0) [set b]
  (@finite_metric_set_borel R [the metricType R of Y] [set b] (@finite_set1 Y b))).
Qed.

(** Source for [area_point_domain]: original one-point partial
    domain in the regression for 3.2.20, p. 256. *)
Local Lemma area_point_domain : partial_function_domain f=[set b].
Proof.
apply/seteqP; split; first by move=> x [y [hx _]].
move=> x hx; exists c; by split.
Qed.

(** Source for [area_point_lipschitz]: the constant map's bound
    zero on its original one-point domain, supporting 3.2.20,
    p. 256. *)
Local Lemma area_point_lipschitz : @is_partial_metric_lipschitz_bound R Y Z f 0.
Proof.
split; first exact: lexx.
by move=> x y u v [_ <-] [_ <-]; rewrite mdistxx mul0r.
Qed.

(** Source for [area_point_count]: N(f,z) is exactly the
    characteristic function of the target singleton in 3.2.20,
    p. 256. This identity checks the actual fibre and
    excludes all ambient extension points. *)
Local Lemma area_point_count z :
  @partial_mapping_multiplicity R Y Z f z=
    (@CharacteristicFunction.value R Z [set c] z)%:E.
Proof.
have hChi := @CharacteristicFunction.laws R Z [set c].
case: (pselect (z=c))=> hz.
- have hFibre : partial_mapping_fibre f z=[set b].
    apply/seteqP; split=> x.
    + by move=> [hx _].
    + move=> hx; split; first exact hx; by rewrite hz.
  rewrite /partial_mapping_multiplicity hFibre counting_measure_singleton_value.
  by rewrite (characteristic_on_set hChi hz).
- have hFibre : partial_mapping_fibre f z=set0.
    apply/seteqP; split=> x; last by move=> [].
    by move=> [hx hcz]; apply: hz; exact: (esym hcz).
  rewrite /partial_mapping_multiplicity hFibre (measure_empty (counting_measure_is_measure R Y)).
  by rewrite (characteristic_off_set hChi hz).
Qed.

(** Source for [area_point_positive_infinite_target]: the target
    integral of the constant positive-infinite weight in the
    positive-atom regression for 3.2.20, p. 256.
    It is infinite by the unit atom, not a null-space identity. *)
Local Lemma area_point_positive_infinite_target :
  is_measure_integral nu (rectifiable_area_target_integrand f (fun _=>+oo%E)) +oo%E.
Proof.
have hm := @hausdorff_measure_is_measure R Z 0.
have hChi := @CharacteristicFunction.laws R Z [set c].
have hC : measure_measurable nu [set c] :=
  @borel_regular_borel_measurable R Z nu hm (@hausdorff_measure_borel_regular R Z 0) [set c]
    (@finite_metric_set_borel R [the metricType R of Z] [set c] (@finite_set1 Z c)).
have hI := @measure_nonnegative_extended_characteristic_integral R Z nu hm [set c]
  (@CharacteristicFunction.value R Z [set c]) +oo%E hChi hC (leey 0%E).
rewrite hausdorff_zero_singleton mule1 in hI.
apply: (@measure_integral_graph_equivalent R Z nu _ _ +oo%E _ hI)=> z t.
change ((+oo* (@CharacteristicFunction.value R Z [set c] z)%:E)%E=t <->
  (+oo* @partial_mapping_multiplicity R Y Z f z)%E=t).
by rewrite area_point_count.
Qed.

(** Source for [point_rectifiable_area_positive_infinity_regression]:
    whole theorem 3.2.20, pp. 256–257, for a map
    with exactly a positive H^0 atom as domain and an extended
    weight identically positive infinity. Both integrals exist
    with value positive infinity, in arbitrary ambient dimensions. *)
Example point_rectifiable_area_positive_infinity_regression :
  is_measure_integral mu (rectifiable_area_source_integrand 0 [set b] f (fun _=>+oo%E)) +oo%E /\
  is_measure_integral nu (rectifiable_area_target_integrand f (fun _=>+oo%E)) +oo%E.
Proof.
have hFormula := @federer_3_2_20 R 0 n k [set b] f (leq0n k)
  area_point_rectifiable area_point_measurable area_point_domain (ex_intro _ 0 area_point_lipschitz)
  (fun _=>+oo%E) +oo%E.
split; [exact: hFormula.2 area_point_positive_infinite_target|exact: area_point_positive_infinite_target].
Qed.

(** Source for [point_rectifiable_area_negative_infinity_regression]:
    whole theorem 3.2.20, pp. 256–257, at the same
    positive H^0 atom with weight identically negative infinity.
    This checks signed reconstruction and the zero-infinity
    convention away from the target image. *)
Example point_rectifiable_area_negative_infinity_regression :
  is_measure_integral mu (rectifiable_area_source_integrand 0 [set b] f (fun _=>-oo%E)) -oo%E /\
  is_measure_integral nu (rectifiable_area_target_integrand f (fun _=>-oo%E)) -oo%E.
Proof.
have hm := @hausdorff_measure_is_measure R Z 0.
have hNeg := measure_integral_negation hm area_point_positive_infinite_target.
have hTarget : is_measure_integral nu (rectifiable_area_target_integrand f (fun _=>-oo%E)) -oo%E.
  apply: (@measure_integral_graph_equivalent R Z nu _ _ -oo%E _ hNeg)=> z t.
  split.
  - move=> [a [ha ht]].
    change ((+oo* @partial_mapping_multiplicity R Y Z f z)%E=a) in ha.
    change ((-oo* @partial_mapping_multiplicity R Y Z f z)%E=t).
    by rewrite -ha -mulNe in ht.
  - move=> ht; exists (+oo* @partial_mapping_multiplicity R Y Z f z)%E.
    split; first reflexivity.
    by rewrite -mulNe.
have hFormula := @federer_3_2_20 R 0 n k [set b] f (leq0n k)
  area_point_rectifiable area_point_measurable area_point_domain (ex_intro _ 0 area_point_lipschitz)
  (fun _=>-oo%E) -oo%E.
split; [exact: hFormula.2 hTarget|exact hTarget].
Qed.

(** Source for [point_intrinsic_approximate_jacobian_zero_regression]:
    the degree-zero definition in 3.2.20, p. 256,
    on an actual approximate-differentiability point of positive
    H^0 mass. Its value is exactly one, with the original
    partial graph rather than an ambient chosen differential. *)
Example point_intrinsic_approximate_jacobian_zero_regression :
  partial_function_graph (measure_approximate_jacobian (measure_restrict mu [set b]) 0 0 f) b 1.
Proof.
have hm := @hausdorff_measure_is_measure R Y 0.
have hr := measure_restrict_is_measure hm [set b].
have hAE := (@federer_3_2_19 R 0 n [set b] area_point_rectifiable area_point_measurable).2
  k f area_point_domain (ex_intro _ 0 area_point_lipschitz).
have hAt : exists d, is_measure_approximate_differential (inner_norm (@euclidean_inner_productP R k))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) (measure_restrict mu [set b]) 0 f b d /\
    partial_function_domain d=measure_approximate_tangent_cone
      (inner_norm_real_norm (@euclidean_inner_productP R n)) (measure_restrict mu [set b]) 0 b.
  apply: contrapT=> hn.
  have hNull : mu [set b]=0%E.
    apply: (measure_null_subset hm _ hAE); by move=> x ->; split.
  have hPos : (0<mu [set b])%E by rewrite hausdorff_zero_singleton lte_fin ltr01.
  by rewrite hNull ltxx in hPos.
have [d [hd hDom]] := hAt.
have hJDom : partial_function_domain
    (measure_approximate_jacobian (measure_restrict mu [set b]) 0 0 f) b.
  rewrite (@measure_approximate_jacobian_domain R n k (measure_restrict mu [set b]) 0 0 f hr); exact hd.1.
have [j hj] := hJDom.
have hj1 := @measure_approximate_jacobian_zero_degree_value R n k (measure_restrict mu [set b]) 0 f b j hj.
by rewrite -hj1.
Qed.
End PointRectifiableArea.

(** Boundary regressions for Federer (1969), 3.2.21,
    p. 257: positive degree over a zero-dimensional target,
    including positive source mass in dimension zero. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanLebesgueDimensions NormDifferentialUP LipschitzUP MeasureUP MeasureBasic MeasureAlmostUP
  MeasureAlmostBasic RectifiableSetUP PureUnrectifiableLaws HausdorffMeasure HausdorffCountableNull
  LinearRankUP TopologicalBorel PointMassMeasure PureUnrectifiableRank.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section PureUnrectifiableRankBoundary.
Variable R:realType.
Local Notation Y:=(inner_metric_space (@euclidean_inner_productP R 0)).

(** Source for [zero_target_positive_degree_pure_regression]:
    positive-degree Hausdorff null targets satisfy the pure
    unrectifiability premise of Federer 3.2.21, p. 257.
    Here the target is the whole one-point Euclidean space. *)
Lemma zero_target_positive_degree_pure_regression:
  is_purely_measure_m_unrectifiable (@hausdorff_measure R Y 1) 1 setT.
Proof.
apply:(@pure_unrectifiable_iff_rectifiable_subsets_null R Y (@hausdorff_measure R Y 1) 1 setT).2.
split; first exact:hausdorff_measure_is_measure.
move=>F hF _.
have hWhole:@hausdorff_measure R Y 1 setT=0%E.
  have hSet:(@setT Y)=[set (0:Y)].
    apply/seteqP; split=>x _; first exact:coordinate_zero; exact:Logic.I.
  by rewrite hSet (hausdorff_positive_degree_singleton_zero (0:Y) (ltn0Sn 0)).
exact:(measure_null_subset (@hausdorff_measure_is_measure R Y 1) hF hWhole).
Qed.

(** Source for [constant_zero_target_rank_regression]: the whole
    conclusion of Federer 3.2.21, p. 257, for
    a constant map into R^0 and positive degree one. The
    source has arbitrary dimension; no degree bound by the
    target dimension is introduced. *)
Lemma constant_zero_target_rank_regression m:
  measure_almost_everywhere (@euclidean_lebesgue_measure R m)
    [set x:R_n R m|exists D r,
      has_norm_differential (inner_norm (@euclidean_inner_productP R m))
        (inner_norm (@euclidean_inner_productP R 0)) setT (fun _:R_n R m=>0) x D /\
      has_linear_rank D r /\ (r<1)%N].
Proof.
have hLip:@is_metric_lipschitz R [the metricType R of inner_metric_space (@euclidean_inner_productP R m)]
    [the metricType R of Y]
    setT (fun _=>0).
  exists 1; split; first exact:ltr01; split; first exact:ler01.
  by move=>x y _ _; rewrite mdistxx mul1r; exact:mdist_ge0.
have h:=@federer_3_2_21 R m 0 1 (fun _=>0) setT (ltn0Sn 0) hLip
  (open_borel_set openT) zero_target_positive_degree_pure_regression.
have hAll:=(measure_almost_everywhere_on_implication _ _ _).1 h.
apply:(measure_almost_everywhere_mono (euclidean_lebesgue_is_measure R m) _ hAll)=>x hx.
exact:(hx Logic.I).
Qed.

(** Source for [positive_atom_pure_unrectifiable_rank_regression]:
    Federer 3.2.21, p. 257, at the source point
    of L^0 mass one. The whole theorem gives an actual
    differential of rank zero there, so its zero-source
    boundary is not a vacuous null-preimage statement. *)
Example positive_atom_pure_unrectifiable_rank_regression:
  exists D,has_norm_differential (inner_norm (@euclidean_inner_productP R 0))
    (inner_norm (@euclidean_inner_productP R 0)) setT (fun _:R_n R 0=>0) 0 D /\
    has_linear_rank D 0%N.
Proof.
have h:=@constant_zero_target_rank_regression 0.
have hAt:exists D r,
    has_norm_differential (inner_norm (@euclidean_inner_productP R 0))
      (inner_norm (@euclidean_inner_productP R 0)) setT (fun _:R_n R 0=>0) 0 D /\
    has_linear_rank D r /\ (r<1)%N.
  apply:contrapT=>hNot.
  have hZero:@euclidean_lebesgue_measure R 0 [set (0:Y)]=0%E.
    apply:(measure_null_subset (euclidean_lebesgue_is_measure R 0) _ h)=>x ->.
    exact hNot.
  have hOne:@euclidean_lebesgue_measure R 0 [set (0:Y)]= 1%E.
    change (point_mass R (0:Y) [set (0:Y)]= 1%E).
    exact:(point_mass_in R (erefl (0:Y))).
  rewrite hOne in hZero.
  by move:hZero=>/eqP; rewrite eqe oner_eq0.
have [D [r [hD [hr hLt]]]]:=hAt.
have hr0:r=0%N by move:hLt; rewrite ltnS leqn0=>/eqP.
exists D; split; first exact hD.
by rewrite hr0 in hr.
Qed.
End PureUnrectifiableRankBoundary.

(** Federer (1969), 3.2.22, pp. 258–260:
    positive-H^0-atom, strict zero-target and signed
    infinite-weight regressions for the whole theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialFunctionPostcomposition PartialMetricLipschitz
  MeasureUP MeasureBasic MeasureRestriction MeasureAlmostUP MeasureAlmostBasic MeasureAlmostEquality
  MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralAlmostEquality MeasureIntegralGraphEquivalence
  MeasureApproximateJacobian MeasureApproximateDifferentialUP MeasureApproximateTangentUP RectifiableTangentPlaneUP
  PartialExteriorNormUP PartialExteriorNormLaws RectifiableSetUP RectifiableElementary
  HausdorffMeasure HausdorffCountingMeasure HausdorffCountableNull HausdorffClosedCoverAgreement
  BorelRegularMeasureUP FiniteExceptionalBorel CountablyMeasureRectifiableOperations
  PositiveCharacteristicMeasurability PartialMappingMultiplicity RectifiableCoarea RealMetricBackground ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section RectifiableCoareaBoundary.
Variable R:realType.
Variables n k:nat.
Variable b:R_n R n.
Variable c:R_n R k.
Local Notation X:=(inner_metric_space (@euclidean_inner_productP R n)).
Local Notation Y:=(inner_metric_space (@euclidean_inner_productP R k)).
Local Notation rho:=(@hausdorff_measure R X 0).
Local Notation alpha:=(@hausdorff_measure R Y 0).
Local Notation f:=(partial_function_source_restrict [set b] (partial_function_total (fun _:R_n R n=>c))).

(** Source for [coarea_point_rectifiable]: positive singleton
    instance of 3.2.14(4), p. 252, supporting
    all three conclusions of 3.2.22, p. 258. *)
Local Lemma coarea_point_rectifiable j (a:R_n R j):
  is_measure_m_rectifiable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R j)) 0) 0 [set a].
Proof.
pose T:=inner_metric_space (@euclidean_inner_productP R j).
have hm:=@hausdorff_measure_is_measure R T 0.
split; last by rewrite hausdorff_zero_singleton; exact:ltry.
split; first exact hm; exists [set a]; split.
- exact:(@rectifiable_countably_rectifiable R T 0 [set a] (@finite_set1 T a)).
- rewrite /measure_almost_included setDv; exact:measure_empty hm.
Qed.

(** Source for [coarea_point_measurable]: singleton Borel
    measurability from 2.10.2(1), p. 171,
    supporting the 3.2.22 boundary tests. *)
Local Lemma coarea_point_measurable j (a:R_n R j) d:
  measure_measurable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R j)) d) [set a].
Proof.
pose T:=inner_metric_space (@euclidean_inner_productP R j).
exact:(@borel_regular_borel_measurable R T _ (@hausdorff_measure_is_measure R T d)
  (@hausdorff_measure_borel_regular R T d) [set a]
  (@finite_metric_set_borel R [the metricType R of T] [set a] (@finite_set1 T a))).
Qed.

(** Source for [coarea_point_almost]: extract the
    actual conclusion at a positive H^0 atom in
    3.2.22(1),(2), p. 258. This prevents
    the regressions from becoming null-space tests. *)
Local Lemma coarea_point_almost j (a:R_n R j) (P:set (R_n R j)):
  measure_almost_everywhere_on (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R j)) 0) [set a] P ->P a.
Proof.
move=>hAE; apply:contrapT=>hNot.
pose T:=inner_metric_space (@euclidean_inner_productP R j).
have hZero:@hausdorff_measure R T 0 [set a]=0%E.
  apply:(measure_null_subset (@hausdorff_measure_is_measure R T 0) _ hAE)=>x ->; by split.
rewrite hausdorff_zero_singleton in hZero.
by move:hZero=>/eqP; rewrite eqe oner_eq0.
Qed.

(** Source for [coarea_point_domain]: exact one-point
    partial domain for 3.2.22, p. 258. *)
Local Lemma coarea_point_domain:partial_function_domain f=[set b].
Proof.
apply/seteqP; split; first by move=>x [y [hx _]].
move=>x hx; exists c; by split.
Qed.

(** Source for [coarea_point_lipschitz]: constant-map
    Lipschitz bound on the original partial domain,
    supporting 3.2.22, p. 258. *)
Local Lemma coarea_point_lipschitz:@is_partial_metric_lipschitz_bound R X Y f 0.
Proof.
split; first exact:lexx.
by move=>x y u v [_ <-] [_ <-]; rewrite mdistxx mul0r.
Qed.

(** Source for [coarea_point_whole]: apply the complete
    3.2.22, p. 258, at two positive H^0
    atoms in arbitrary ambient Euclidean dimensions. *)
Local Lemma coarea_point_whole:is_rectifiable_coarea 0 0 [set b] [set c] f.
Proof.
apply:(@federer_3_2_22 R 0 n 0 k [set b] [set c] f (leqnn 0)
  (coarea_point_rectifiable b) (coarea_point_measurable b 0)
  (coarea_point_rectifiable c) (coarea_point_measurable c 0) coarea_point_domain
  (ex_intro _ 0 coarea_point_lipschitz)).
by move=>z [x [_ <-]].
Qed.

(** Source for [point_rectifiable_coarea_image_regression]:
    whole 3.2.22(1), p. 258, at a positive
    source atom. The actual zero-degree Jacobian is
    one, forcing the exact zero-dimensional target
    tangent image rather than its zero-Jacobian alternative. *)
Example point_rectifiable_coarea_image_regression:
  exists d:partial_function (R_n R n) (R_n R k),
    is_measure_approximate_differential (inner_norm (@euclidean_inner_productP R k))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) (measure_restrict rho [set b]) 0 f b d /\
    is_partial_exterior_norm 0 d 1 /\
    partial_function_range d=measure_approximate_tangent_cone (inner_norm_real_norm (@euclidean_inner_productP R k))
      (measure_restrict alpha [set c]) 0 c /\
    is_m_dimensional_approximate_tangent 0 (measure_restrict alpha [set c]) c.
Proof.
have hAt:=coarea_point_almost (rectifiable_coarea_image_law coarea_point_whole).
have [z [d [j [hValue [hApprox [hNorm hAlternative]]]]]]:=hAt.
have hZ:z=c:=esym hValue.2.
have hJ:j= 1:=partial_exterior_norm_unique hNorm (partial_exterior_norm_zero_degree d).
rewrite hJ hZ in hNorm hAlternative.
have [hZero|[hImage hPlane]]:=hAlternative.
- by move:hZero=>/eqP; rewrite oner_eq0.
- exists d; split; first exact hApprox; split; first exact hNorm; by split.
Qed.

(** Source for [point_rectifiable_coarea_fibre_regression]:
    whole 3.2.22(2), p. 258, at a positive
    target atom with m=mu=0. The actual fibre
    is finite-mass rectifiable and measurable. *)
Example point_rectifiable_coarea_fibre_regression:
  is_measure_m_rectifiable rho 0 (partial_mapping_fibre f c) /\
  measure_measurable rho (partial_mapping_fibre f c).
Proof.
exact:(coarea_point_almost (rectifiable_coarea_fibre_law coarea_point_whole)).
Qed.

(** Source for [coarea_point_extended_weight_integrable]:
    supporting infinite-weight regression of the printed
    3.2.22(3) theorem, p. 258. A nonnegative
    extended constant is integrable on the positive atom;
    its original partial domain remains exactly that atom. *)
Local Lemma coarea_point_extended_weight_integrable (q : \bar R):(0<=q)%E ->
  is_measure_integrable (measure_restrict rho [set b])
    (partial_function_source_restrict [set b] (partial_function_total (fun _:R_n R n=>(q:extended_real_line R)))).
Proof.
move=>hq.
pose nu:=measure_restrict rho [set b].
have hr:=@hausdorff_measure_is_measure R X 0.
have hn:=measure_restrict_is_measure hr [set b].
have hConst:=@PositiveCharacteristicMeasurability.nonnegative_extended_constant_integral R X nu hn q hq.
have hSupport:measure_almost_everywhere nu [set b].
  rewrite /measure_almost_everywhere /nu /measure_restrict.
  have hEmpty:[set b] `&` (~` [set b])=set0 by apply/seteqP; split=>[x [hx hNot]|x []]; exact:hNot hx.
  rewrite hEmpty; exact:measure_empty hr.
exists (q*nu setT)%E.
apply:(measure_integral_almost_equal hn hConst).
apply:(measure_almost_everywhere_mono hn _ hSupport)=>x hx.
exists q; split; first reflexivity; by split.
Qed.

(** Source for [point_rectifiable_coarea_infinite_weight_regression]:
    whole extended-real-weight assertion 3.2.22(3),
    pp. 258, 260. A positive-infinite weight on
    the source H^0 atom remains admissible; replacing
    integrability by finite summability would break this test. *)
Example point_rectifiable_coarea_infinite_weight_regression:
  let g:=partial_function_source_restrict [set b]
    (partial_function_total (fun _:R_n R n=>(+oo%E:extended_real_line R))) in
  exists a,is_measure_integral rho (rectifiable_coarea_source_integrand 0 0 [set b] f g) a /\
    is_measure_subset_integral alpha [set c] (rectifiable_coarea_fibre_integral 0 0 f g) a.
Proof.
move=>g.
have hGDomain:partial_function_domain g=[set b].
  apply/seteqP; split; first by move=>x [y [hx _]].
  move=>x hx; exists +oo%E; by split.
exact:(@rectifiable_coarea_integral_law R 0 n 0 k [set b] [set c] f coarea_point_whole g
  hGDomain (coarea_point_extended_weight_integrable (leey 0%E))).
Qed.

(** Source for [strict_zero_target_coarea_fibre_regression]:
    whole 3.2.22(2), p. 258, with m=1>mu=0.
    The positive H^0 target atom has its actual
    H^1-null source singleton as a measurable rectifiable
    fibre. This checks the strict zero-target boundary
    without discarding the target point as exceptional. *)
Example strict_zero_target_coarea_fibre_regression:
  is_measure_m_rectifiable (@hausdorff_measure R X 1) 1 (partial_mapping_fibre f c) /\
  measure_measurable (@hausdorff_measure R X 1) (partial_mapping_fibre f c).
Proof.
have hNull:@hausdorff_measure R X 1 [set b]=0%E:=@hausdorff_positive_degree_singleton_zero R X 1 b (ltn0Sn 0).
have hRect:is_measure_m_rectifiable (@hausdorff_measure R X 1) 1 [set b].
  split; first exact:(@countably_measure_rectifiable_null R X (@hausdorff_measure R X 1) 1 [set b]
    (@hausdorff_measure_is_measure R X 1) hNull).
  by rewrite hNull; exact:ltry.
have hRange:partial_function_range f `<=` [set c] by move=>z [x [_ <-]].
have hAE:=@federer_3_2_22_2 R 1 n 0 k [set b] [set c] f (leq0n 1) hRect
  (coarea_point_measurable b 1) (coarea_point_rectifiable c) (coarea_point_measurable c 0)
  coarea_point_domain (ex_intro _ 0 coarea_point_lipschitz) hRange.
exact:(coarea_point_almost hAE).
Qed.
End RectifiableCoareaBoundary.

(** Federer (1969), 3.2.23, p. 260: multipoint zero-dimensional
    source and target regressions. Four product atoms test the finite-set
    convention, and a nonrectangular two-point diagonal tests the full
    measure law beyond a rectangle's total mass. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates EuclideanCartesianMap RectifiableCartesianProduct
  RectifiableFiniteHausdorffMass RectifiableSetUP HausdorffMeasure HausdorffCountingMeasure
  HausdorffClosedCoverAgreement MeasureUP MeasureFiniteAdditivity MeasureRestriction MeasurePushforward
  BorelRegularMeasureUP FiniteExceptionalBorel ProductMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Section RectifiableCartesianBoundary.
Variable R:realType.
Variables n v:nat.
Local Notation X:=(inner_metric_space (@euclidean_inner_productP R n)).
Local Notation Y:=(inner_metric_space (@euclidean_inner_productP R v)).
Local Notation T:=(inner_metric_space (@euclidean_inner_productP R (n+v))).
Variables b0 b1:X.
Variables c0 c1:Y.
Hypotheses (hSourceDifferent:b0!=b1) (hTargetDifferent:c0!=c1).
Local Notation W:=([set b0] `|` [set b1]).
Local Notation Z:=([set c0] `|` [set c1]).
Local Notation Diagonal:=([set (b0,c0)] `|` [set (b1,c1)]).
Local Notation alpha:=(measure_restrict (@hausdorff_measure R X 0) W).
Local Notation beta:=(measure_restrict (@hausdorff_measure R Y 0) Z).
Local Notation ha:=(measure_restrict_is_measure (@hausdorff_measure_is_measure R X 0) W).
Local Notation hb:=(measure_restrict_is_measure (@hausdorff_measure_is_measure R Y 0) Z).

(** Source for [cartesian_pair_whole]: supporting whole-theorem
    application in the zero-dimensional finite-set convention of
    3.2.14, p. 252, for Federer 3.2.23, p. 260.
    Each factor has two distinct points, so a single R^0
    parametrization of either whole factor would be insufficient. *)
Local Lemma cartesian_pair_whole:is_rectifiable_cartesian_product 0 0 W Z.
Proof.
have hW:finite_set W by rewrite finite_setU; split; exact:finite_set1.
have hZ:finite_set Z by rewrite finite_setU; split; exact:finite_set1.
exact:(@federer_3_2_23 R 0 0 n v W Z hW (finite_metric_set_borel hW)
  (@rectifiable_hausdorff_measure_rectifiable R 0 v Z hZ) (finite_metric_set_borel hZ)).
Qed.

(** Source for [cartesian_pair_mass]: supporting atom count
    for the 3.2.23 regression, p. 260. The source convention
    is H^0 counting measure in 2.10.2, p. 171; disjoint
    unit atoms have mass two by 2.1.3, p. 55. *)
Local Lemma cartesian_pair_mass (S:metricType R) (x y:S):x!=y ->
  @hausdorff_measure R S 0 ([set x] `|` [set y])=(2%R:R)%:E.
Proof.
move=>hDifferent.
have hMeas:=borel_regular_borel_measurable (@hausdorff_measure_is_measure R S 0)
  (@hausdorff_measure_borel_regular R S 0) (finite_metric_set_borel (finite_set1 x)).
have hDisjoint:forall t,[set x] t ->[set y] t ->False.
  move=>t hx hy; have he:x=y:=eq_trans (esym hx) hy.
  by move:hDifferent; rewrite he eqxx.
rewrite (measure_disjoint_union hMeas hDisjoint) !hausdorff_zero_singleton.
by rewrite -EFinD.
Qed.

(** Source for [zero_degree_cartesian_four_atoms_regression]:
    the complete theorem 3.2.23, p. 260, applied to two
    positive H^0 atoms in each factor. The exact product
    has mass four and satisfies both independent whole-theorem
    laws, including equality on every test subset. *)
Example zero_degree_cartesian_four_atoms_regression:
  is_rectifiable_cartesian_product 0 0 W Z /\
  @hausdorff_measure R T 0 (euclidean_cartesian_set W Z)=(4%R:R)%:E.
Proof.
split; first exact cartesian_pair_whole.
have hMass:=rectifiable_cartesian_total_mass_from_identity
  (rectifiable_cartesian_measure_law cartesian_pair_whole).
rewrite (cartesian_pair_mass hSourceDifferent) (cartesian_pair_mass hTargetDifferent) -EFinM -natrM in hMass.
exact hMass.
Qed.

(** Source for [nonrectangular_cartesian_diagonal_regression]: the
    full restricted-measure equality of Federer 3.2.23, p. 260,
    on a two-point diagonal which cannot be a rectangle. This
    application requires the entire measure law and cannot be replaced
    by a formula only for the mass of W times Z. *)
Example nonrectangular_cartesian_diagonal_regression:
  (~exists (A:set X) (B:set Y),Diagonal=A `*` B) /\
  @hausdorff_measure R T 0 (euclidean_cartesian_set W Z `&`
    ((@euclidean_block_split R n v) @^-1` Diagonal))=
    product_measure ha hb Diagonal.
Proof.
split.
- move=>[A [B hRectangle]].
  have h00:Diagonal (b0,c0) by left.
  have h11:Diagonal (b1,c1) by right.
  rewrite hRectangle in h00.
  rewrite hRectangle in h11.
  have h01:Diagonal (b0,c1).
    rewrite hRectangle; split; [exact h00.1|exact h11.2].
  have [hEqual|hEqual]:=h01.
  + have he:c1=c0:=congr1 snd hEqual.
    by move:hTargetDifferent; rewrite he eqxx.
  + have he:b0=b1:=congr1 fst hEqual.
    by move:hSourceDifferent; rewrite he eqxx.
- have h:=congr1 (fun rho=>rho Diagonal) (rectifiable_cartesian_measure_law cartesian_pair_whole).
  exact h.
Qed.
End RectifiableCartesianBoundary.

(** Federer (1969), 3.2.24, p. 260: regressions use the
    proved Cantor counterexample itself, not only a conditional
    counterexample predicate. They force both genuine failures. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanCartesianMap RectifiableCartesianCounterexample RectifiableCartesianCounterexampleConsequences
  RectifiableCartesianProductUP RectifiableSetUP HausdorffMeasure MeasureUP MeasureRestriction ProductMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weakened_rectifiable_cartesian_theorem_false_regression]:
    the warning in 3.2.24, p. 260, formally refutes
    replacing genuine first-factor rectifiability in the whole
    theorem by finite-mass measure rectifiability, even for
    Borel factors with zero masses in fixed dimensions. *)
Example weakened_rectifiable_cartesian_theorem_false_regression (R:realType):
  ~(forall W Z:set (R_n R 4),is_rectifiable_cartesian_counterexample W Z ->
    is_rectifiable_cartesian_product 2 2 W Z).
Proof.
move=>hWeak; have [W [Z hExample]]:=federer_3_2_24 R.
exact:(rectifiable_cartesian_counterexample_not_rectifiable hExample
  (rectifiable_cartesian_rectifiability_law (hWeak W Z hExample))).
Qed.

(** Source for [null_factors_infinite_cartesian_product_regression]:
    both zero factor masses and infinite product mass in
    3.2.24, p. 260, are realized by actual existing
    naturally normalized Hausdorff measures. The reference product
    is zero on every test subset. *)
Example null_factors_infinite_cartesian_product_regression (R:realType):
  exists W Z:set (R_n R 4),
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (4+4))) 4
      (euclidean_cartesian_set W Z)=+oo /\
    forall S,product_measure
      (measure_restrict_is_measure (@hausdorff_measure_is_measure R
        (inner_metric_space (@euclidean_inner_productP R 4)) 2) W)
      (measure_restrict_is_measure (@hausdorff_measure_is_measure R
        (inner_metric_space (@euclidean_inner_productP R 4)) 2) Z) S=0.
Proof.
have [W [Z hExample]]:=federer_3_2_24 R.
exists W,Z; split; first exact:(cartesian_counterexample_product_infinite hExample).
exact:(rectifiable_cartesian_counterexample_reference_zero hExample).
Qed.

(** Federer (1969), 3.2.25, p. 261: positive-atom
    degree-zero and genuinely nonmeasurable positive-length source
    regressions. Both use the complete existential theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import ModuleQuotient GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanLinearMaps InnerNorm InnerMetric InnerExteriorPositivity ExteriorGrading ExteriorNorm AssociatedSubspace
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialMetricLipschitz
  CoveringFamilyUP RectifiableSetUP RectifiableOrientation RectifiableFiniteHausdorffMass
  HausdorffMeasure HausdorffCountingMeasure HausdorffCountableNull HausdorffClosedCoverAgreement
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasureSplit MeasureFiniteClosure
  BernsteinNonmeasurableSubset EuclideanMetricCompleteness EuclideanMetricSeparability
  EuclideanHausdorffLebesgue EuclideanLebesgueBoxes EuclideanLebesgueHaar
  MetricBoundedClosureLaws CompactMetricBounded CompactSetDistanceProfile.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [orientation_atom_almost_property]: the
    H^0 singleton mass in 2.10.2(1), p. 171, makes
    the degree-zero application of 3.2.25, p. 261,
    hold at its actual source atom. *)
Local Lemma orientation_atom_almost_property (R:realType) n (a:R_n R n) (P:set (R_n R n)):
  measure_almost_everywhere_on (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) 0) [set a] P ->P a.
Proof.
move=>hAE; apply:contrapT=>hNot.
have hNull:@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) 0 [set a]=0.
  apply:(measure_null_subset (@hausdorff_measure_is_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) 0) _ hAE).
  by move=>x ->; split.
have hPositive:(0<@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) 0 [set a])%E.
  by rewrite hausdorff_zero_singleton lte_fin ltr01.
by rewrite hNull ltxx in hPositive.
Qed.

(** Source for [orientation_bounded_line_rectifiable]: identity
    parametrization in 3.2.14(1), p. 251, supplies
    genuine one-rectifiability of the bounded nonmeasurable source
    used to test the scope of 3.2.25, p. 261. *)
Local Lemma orientation_bounded_line_rectifiable (R:realType)
    (W:set (inner_metric_space (@euclidean_inner_productP R 1))):
  metric_set_bounded W ->@is_m_rectifiable R
    (inner_metric_space (@euclidean_inner_productP R 1)) 1 W.
Proof.
move=>hBounded.
pose X:=inner_metric_space (@euclidean_inner_productP R 1).
pose f:=partial_function_source_restrict W (partial_function_total (fun x:X=>x)).
exists f; split.
- by rewrite /f partial_function_source_restrict_domain partial_function_total_domain setIT.
- split.
  + exists 1%R; split; first exact:ler01.
    move=>x y a b [hx hxa] [hy hyb].
    change (x=a) in hxa; change (y=b) in hyb.
    by rewrite -hxa -hyb mul1r.
  + apply/seteqP; split=>y.
    * by move=>[x [hx hxy]]; rewrite -hxy.
    * move=>hy; exists y; by split.
Qed.

(** Source for [zero_degree_orientation_atom_regression]: the
    whole theorem 3.2.25, p. 261, at a positive
    H^0 source atom. It forces an actual defined simple
    unit value and cannot discard the atom as exceptional. *)
Example zero_degree_orientation_atom_regression (R:realType) n (a:R_n R n):
  exists T:partial_function (R_n R n) (exterior_power (R_n R n) 0),
    is_rectifiable_measurable_orientation [set a] T /\
    exists xi,partial_function_graph T a xi /\simple xi /\
      @exterior_norm R (euclidean_two_nonzero R) (R_n R n)
        (@euclidean_inner_product R n) (@euclidean_inner_productP R n) 0 xi= 1%R.
Proof.
have hRect:=@rectifiable_hausdorff_measure_rectifiable R 0 n [set a] (@finite_set1 _ a).
have [T [hWhole hDomain]]:=federer_3_2_25 hRect.
have hAt:=orientation_atom_almost_property (rectifiable_orientation_tangent hWhole).
have [xi [hGraph hRest]]:=hAt.
have [hSimple hUnit]:=rectifiable_orientation_unit_simple hWhole hGraph.
exists T; split; first exact hWhole; exists xi; by split; last split.
Qed.

(** Source for [nonmeasurable_positive_length_orientation_regression]:
    the lack of a W-measurability hypothesis in 3.2.25,
    p. 261, tested on an actual nonmeasurable positive-H^1
    subset of the unit interval in R^1. Existence follows
    from 2.2.4, p. 62; the whole orientation field
    remains measurable under H^1 restricted to that source. *)
Example nonmeasurable_positive_length_orientation_regression (R:realType):
  exists (W:set (R_n R 1)) (T:partial_function (R_n R 1) (exterior_power (R_n R 1) 1)),
    ~measure_measurable (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R 1)) 1) W /\
    (0<@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 1)) 1 W)%E /\
    is_rectifiable_measurable_orientation W T /\partial_function_domain T `<=` W.
Proof.
pose X:=inner_metric_space (@euclidean_inner_productP R 1).
pose H:=@hausdorff_measure R X 1.
pose A:set X:=[set x|forall i,0<x i<1]%R.
pose Q:set X:=[set x|forall i,0<=x i<= 1]%R.
have hH:=@hausdorff_measure_is_measure R X 1.
have hMass:H A= 1.
  by rewrite /H (euclidean_hausdorff_spherical_lebesgue A).1 euclidean_unit_cube.
have hPositive:0<H A by rewrite hMass lte_fin ltr01.
have hFinite:H A< +oo by rewrite hMass ltry.
have [W [hWA hNot]]:=@borel_regular_nonmeasurable_subset R X H hH
  (@hausdorff_measure_borel_regular R X 1) A (@euclidean_metric_complete R 1)
  (@euclidean_metric_separable R 1) hPositive hFinite
  (fun x _=>@hausdorff_positive_degree_singleton_zero R X 1 x (erefl true)).
have hQCompact:@compact X Q:=@euclidean_closed_box_compact R 1%N (fun _:'I_1=>0%R) (fun _:'I_1=>1%R).
have hQNonempty:Q!=set0.
  exists (0%R:X); move=>i; by rewrite ffunE ler01 lexx.
pose CQ:compact_metric_set X:=exist _ Q (mem_set (conj hQCompact hQNonempty)).
have hWQ:W `<=` Q.
  move=>x hx i; have /andP[h0 h1]:=hWA x hx i; apply/andP; split; exact:ltW.
have hBounded:metric_set_bounded W:=metric_bounded_subset hWQ (compact_metric_diameter_finite CQ).
have hRect:=rectifiable_hausdorff_measure_rectifiable (orientation_bounded_line_rectifiable hBounded).
have hWPositive:0<H W.
  rewrite lt_neqAle (measure_nonnegative hH W) andbT; apply/negP=>/eqP hZero.
  apply:hNot; exact:(@measure_null_measurable R [the choiceType of X] H hH W (esym hZero)).
have [T hWhole]:=federer_3_2_25 hRect.
exists W,T; split; first exact hNot; split; first exact hWPositive; exact hWhole.
Qed.

(** Federer (1969), 3.2.26, p. 261: positive-atom
    degree-zero and genuinely nonmeasurable positive-length source
    regressions. Both use the complete six-measure theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import RectifiableGeometricMeasureEquality IntegralGeometricMeasure ProjectionMeasure ExteriorMeasure
  ModuleQuotient GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanLinearMaps InnerNorm InnerMetric InnerExteriorPositivity ExteriorGrading ExteriorNorm AssociatedSubspace
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialMetricLipschitz
  CoveringFamilyUP RectifiableSetUP RectifiableFiniteHausdorffMass
  HausdorffMeasure HausdorffCountingMeasure HausdorffCountableNull HausdorffClosedCoverAgreement
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasureSplit MeasureFiniteClosure
  BernsteinNonmeasurableSubset EuclideanMetricCompleteness EuclideanMetricSeparability
  EuclideanHausdorffLebesgue EuclideanLebesgueBoxes EuclideanLebesgueHaar
  MetricBoundedClosureLaws CompactMetricBounded CompactSetDistanceProfile.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [geometric_bounded_line_rectifiable]: identity
    parametrization in 3.2.14(1), p. 251, supplies
    genuine one-rectifiability of the bounded nonmeasurable source
    used to test the scope of 3.2.26, p. 261. *)
Local Lemma geometric_bounded_line_rectifiable (R:realType)
    (W:set (inner_metric_space (@euclidean_inner_productP R 1))):
  metric_set_bounded W ->@is_m_rectifiable R
    (inner_metric_space (@euclidean_inner_productP R 1)) 1 W.
Proof.
move=>hBounded.
pose X:=inner_metric_space (@euclidean_inner_productP R 1).
pose f:=partial_function_source_restrict W (partial_function_total (fun x:X=>x)).
exists f; split.
- by rewrite /f partial_function_source_restrict_domain partial_function_total_domain setIT.
- split.
  + exists 1%R; split; first exact:ler01.
    move=>x y a b [hx hxa] [hy hyb].
    change (x=a) in hxa; change (y=b) in hyb.
    by rewrite -hxa -hyb mul1r.
  + apply/seteqP; split=>y.
    * by move=>[x [hx hxy]]; rewrite -hxy.
    * move=>hy; exists y; by split.
Qed.

(** Source for [zero_degree_geometric_measure_atom_regression]: the
    complete six-measure equality in 3.2.26, p. 261,
    tested at a positive H^0 atom, at every finite
    exponent and at infinity. None of the values is
    obtained by discarding the singleton as exceptional. *)
Example zero_degree_geometric_measure_atom_regression (R:realType) n (a:R_n R n):
  @spherical_measure R (inner_metric_space (@euclidean_inner_productP R n)) 0 [set a]= 1 /\
  @exterior_diameter_measure R n 0 [set a]= 1 /\
  @gross_measure R n 0 [set a]= 1 /\
  forall t: \bar R,1<=t ->
    @convex_integral_geometric_measure R n 0 (leq0n n) t [set a]= 1 /\
    @integral_geometric_measure R n 0 (leq0n n) t [set a]= 1.
Proof.
have hRect:=@rectifiable_hausdorff_measure_rectifiable R 0 n [set a] (@finite_set1 _ a).
have hWhole:=@federer_3_2_26 R 0 n (leq0n n) [set a] hRect.
by rewrite hausdorff_zero_singleton in hWhole.
Qed.

(** Source for [nonmeasurable_geometric_measure_regression]: the
    arbitrary-source scope of the whole theorem 3.2.26,
    pp. 261–262, on an actual nonmeasurable positive-H^1
    subset of the unit interval. The finite exponent two
    tests the integral-geometric equality beyond the
    infinity endpoint; spherical equality is also retained. *)
Example nonmeasurable_geometric_measure_regression (R:realType):
  exists W:set (R_n R 1),
    ~measure_measurable (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R 1)) 1) W /\
    (0<@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 1)) 1 W)%E /\
    @spherical_measure R (inner_metric_space (@euclidean_inner_productP R 1)) 1 W=
      @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 1)) 1 W /\
    @integral_geometric_measure R 1 1 (leqnn 1) 2%R%:E W=
      @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 1)) 1 W.
Proof.
pose X:=inner_metric_space (@euclidean_inner_productP R 1).
pose H:=@hausdorff_measure R X 1.
pose A:set X:=[set x|forall i,0<x i<1]%R.
pose Q:set X:=[set x|forall i,0<=x i<= 1]%R.
have hH:=@hausdorff_measure_is_measure R X 1.
have hMass:H A= 1.
  by rewrite /H (euclidean_hausdorff_spherical_lebesgue A).1 euclidean_unit_cube.
have hPositive:0<H A by rewrite hMass lte_fin ltr01.
have hFinite:H A< +oo by rewrite hMass ltry.
have [W [hWA hNot]]:=@borel_regular_nonmeasurable_subset R X H hH
  (@hausdorff_measure_borel_regular R X 1) A (@euclidean_metric_complete R 1)
  (@euclidean_metric_separable R 1) hPositive hFinite
  (fun x _=>@hausdorff_positive_degree_singleton_zero R X 1 x (erefl true)).
have hQCompact:@compact X Q:=@euclidean_closed_box_compact R 1%N (fun _:'I_1=>0%R) (fun _:'I_1=>1%R).
have hQNonempty:Q!=set0.
  exists (0%R:X); move=>i; by rewrite ffunE ler01 lexx.
pose CQ:compact_metric_set X:=exist _ Q (mem_set (conj hQCompact hQNonempty)).
have hWQ:W `<=` Q.
  move=>x hx i; have /andP[h0 h1]:=hWA x hx i; apply/andP; split; exact:ltW.
have hBounded:metric_set_bounded W:=metric_bounded_subset hWQ (compact_metric_diameter_finite CQ).
have hRect:=rectifiable_hausdorff_measure_rectifiable (geometric_bounded_line_rectifiable hBounded).
have hWPositive:0<H W.
  rewrite lt_neqAle (measure_nonnegative hH W) andbT; apply/negP=>/eqP hZero.
  apply:hNot; exact:(@measure_null_measurable R [the choiceType of X] H hH W (esym hZero)).
have [hS [_ [_ hMeasures]]]:=@federer_3_2_26 R 1 1 (leqnn 1) W hRect.
have [hQ hI]:=hMeasures 2%R%:E (lee_tofin (ler1n R 2)).
exists W; split; first exact hNot; split; first exact hWPositive; by split.
Qed.

(** Federer (1969), 3.2.27, pp. 262–263: a
    positive degree-zero atom tests the actual coordinate
    integral values. The positive-length nonmeasurable
    two-sheet example tests the preserved lower bound
    and the necessity of the upper-bound correction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  ExteriorIndices ExteriorDeterminant SingleCoordinateProjection
  RectifiableSetUP RectifiableFiniteHausdorffMass RectifiableCoordinateMassUP CoordinateMassMonotonicity
  RectifiableCoordinateProjectionBounds RectifiableCoordinateLower
  RectifiableCoordinateCounterexampleUP RectifiableCoordinateCounterexample
  HausdorffMeasure HausdorffCountingMeasure MeasureUP MeasureSplit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [zero_degree_coordinate_index_sum]: the
    single empty coordinate index in the degree-zero
    case of 3.2.27, p. 262, by the top-power
    convention of 1.3.4, p. 16. *)
Local Lemma zero_degree_coordinate_index_sum (R:realType) (f:Lambda 0 0->R):
  (\sum_lambda f lambda)%R=f (Lambda_top 0).
Proof.
rewrite (bigD1 (Lambda_top 0)) //=.
have hZero:(\sum_(lambda:Lambda 0 0|lambda!=Lambda_top 0) f lambda)%R=0%R.
  apply:big1=>lambda hn; exfalso.
  by move:hn; rewrite (Lambda_top_unique lambda) eqxx.
by rewrite hZero addr0.
Qed.

(** Source for [zero_degree_coordinate_mass_atom_regression]:
    the whole existence and both bounds of 3.2.27,
    pp. 262–263, applied to the positive H^0 atom
    in R^0. The actual empty-coordinate integral is
    forced to be one, rather than lost as exceptional. *)
Example zero_degree_coordinate_mass_atom_regression (R:realType):
  exists a:Lambda 0 0->R,
    is_rectifiable_coordinate_masses [set (0%R:R_n R 0)] a /\a (Lambda_top 0)= 1%R.
Proof.
pose X:=inner_metric_space (@euclidean_inner_productP R 0).
pose W:set X:=[set (0%R:X)].
pose H:=@hausdorff_measure R X 0.
have hH:=@hausdorff_measure_is_measure R X 0.
have hRect:=@rectifiable_hausdorff_measure_rectifiable R 0 0 W (@finite_set1 X (0%R:X)).
have hWhole:W=setT.
  apply/seteqP; split; first by move=>x _.
  by move=>x _; rewrite /W (coordinate_zero x).
have hW:measure_measurable H W by rewrite hWhole; exact:measure_measurable_whole hH.
have [a [hMasses [hLower hUpper]]]:=@rectifiable_coordinate_integrals_exist R 0 0 (leqnn 0) W hRect hW.
have hNonnegative:=@coordinate_masses_nonnegative R 0 0 W a hMasses (Lambda_top 0).
rewrite /W hausdorff_zero_singleton (@zero_degree_coordinate_index_sum R a) lee_fin in hUpper.
rewrite /W hausdorff_zero_singleton
  (@zero_degree_coordinate_index_sum R (fun lambda=>((a lambda)^+2)%R)) sqrtr_sqr
  (ger0_norm hNonnegative) lee_fin in hLower.
exists a; split; first exact hMasses.
apply/eqP; by rewrite eq_le hLower hUpper.
Qed.

(** Source for [nonmeasurable_coordinate_lower_and_upper_failure_regression]:
    the local correction to the upper bound of
    3.2.27, pp. 262–263, while its lower bound
    retains the printed arbitrary-source scope. Apply
    that lower theorem to the same genuinely rectifiable,
    nonmeasurable positive-length example with actual
    coordinate integral values one and zero. *)
Example nonmeasurable_coordinate_lower_and_upper_failure_regression (R:realType):
  exists (W:set (R_n R 2)) (a:Lambda 2 1->R),
    is_rectifiable_coordinate_masses W a /\
    ~measure_measurable (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R 2)) 1) W /\
    (Num.sqrt (\sum_lambda (a lambda)^+2))%:E<=
      @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 2)) 1 W /\
    (\sum_lambda a lambda)%R%:E<
      @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 2)) 1 W /\
    a (single_coordinate_selection (ord0:'I_2))= 1%R /\
    a (single_coordinate_selection (ord_max:'I_2))=0%R.
Proof.
have [W [a hExample]]:=rectifiable_coordinate_upper_requires_measurability R.
have hMasses:=coordinate_counterexample_integrals hExample.
have hLower:=@rectifiable_coordinate_projection_lower R 1 2 (erefl true) W a
  (coordinate_counterexample_finite_rectifiable hExample) hMasses.
have hFailure:(\sum_lambda a lambda)%R%:E<
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 2)) 1 W.
  by rewrite (coordinate_counterexample_sum hExample); exact:coordinate_counterexample_excess hExample.
exists W,a; split; first exact hMasses; split; first exact:coordinate_counterexample_nonmeasurable hExample.
split; first exact hLower; split; first exact hFailure.
exact:coordinate_counterexample_values hExample.
Qed.

(** Federer (1969), 3.2.28(2)–(5), pp. 265–267:
    regression values for actual Hausdorff volumes,
    including empty products and positive H^0 atoms. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal topology.
From Federer Require Import EuclideanManifoldVolumes EuclideanStiefelEmptyFrameVolume StiefelGrassmannBoundaryValues
  EulerGamma EulerGammaHalfParameters.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [federer_3_2_28_empty_frame_atom]: degree-zero
    regression supporting the induction of Federer
    3.2.28(5), p. 267. The unique empty frame
    has positive H^0 mass one even in zero ambient
    dimension; no erroneous orientation factor two applies. *)
Example federer_3_2_28_empty_frame_atom (R:realType):
  euclidean_stiefel_volume R 0 0= 1.
Proof. exact:(@euclidean_stiefel_empty_frame_volume R 0). Qed.

(** Source for [federer_3_2_28_first_frame_gamma]: the actual
    sphere base of the printed Stiefel induction,
    Federer 3.2.28(5), p. 267, and 3.2.13,
    p. 251, including a zero-dimensional sphere. *)
Example federer_3_2_28_first_frame_gamma (R:realType) n (hPos:(0<n)%N):
  euclidean_stiefel_volume R n 1=
    (2*(euler_gamma_half R)^+n/euler_gamma (@positive_dimension_half R n hPos))%R%:E.
Proof. exact:(@euclidean_first_frame_gamma_volume R n hPos). Qed.

(** Source for [federer_3_2_28_full_plane_atom]: the actual
    G(n,n) target is one positive H^0 atom,
    Federer 3.2.28(4),(5), p. 267. *)
Example federer_3_2_28_full_plane_atom (R:realType) n:
  (0<n)%N ->euclidean_grassmann_volume R n n= 1.
Proof. exact:(@euclidean_full_grassmann_volume R n). Qed.

(** Source for [federer_3_2_28_full_plane_two_orientations]:
    Go(n,n) consists of two positive H^0 atoms,
    Federer 3.2.28(2),(4), pp. 265,267. This
    tests the orientation factor at zero manifold dimension. *)
Example federer_3_2_28_full_plane_two_orientations (R:realType) n:
  (0<n)%N ->euclidean_oriented_grassmann_volume R n n=(2:R)%:E.
Proof. exact:(@euclidean_full_oriented_grassmann_volume R n). Qed.

(** Federer (1969), 3.2.29, pp. 267–268: regressions
    for positive zero-dimensional atoms and higher-degree null
    sources, without silently imposing m<=n or finite mass. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  RectifiableSetUP RectifiableManifoldCoverUP RectifiableManifoldCharacterisation
  HausdorffMeasure HausdorffCountingMeasure HausdorffCountableNull MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_3_2_29_zero_atom_covered]: regression
    for the zero-degree boundary of Federer 3.2.29, p. 267.
    The almost-cover law forces the actual positive H^0 atom into
    the union; a missing atom cannot be hidden in a null exception. *)
Example federer_3_2_29_zero_atom_covered (R:realType) n (x:R_n R n)
    (C:set (set (R_n R n))):
  is_countable_submanifold_measure_cover 0 1 [set x] C ->
  (\bigcup_(S in C) S) x.
Proof.
move=>hC; case:(pselect ((\bigcup_(S in C) S) x))=>hx; first exact hx.
exfalso; rename hx into hn.
have hSub:[set x] `<=` [set x] `\` \bigcup_(S in C) S.
  by move=>y ->; split.
have hZero:=measure_null_subset (@hausdorff_measure_is_measure R
  (inner_metric_space (@euclidean_inner_productP R n)) 0) hSub (submanifold_measure_cover_almost hC).
rewrite hausdorff_zero_singleton in hZero.
by move:hZero=>/eqP; rewrite eqe oner_eq0.
Qed.

(** Source for [federer_3_2_29_above_ambient_null_point]: regression
    for the absence of a dimension bound in Federer 3.2.29,
    p. 267. A point in R^0 is countably (H^1,1)
    rectifiable and has the empty manifold family as an almost
    cover: no one-dimensional manifold in R^0 is required. *)
Example federer_3_2_29_above_ambient_null_point (R:realType) (x:R_n R 0):
  is_countably_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R 0)) 1) 1 [set x] /\
  is_countable_submanifold_measure_cover 1 1 [set x] set0.
Proof.
have hCover:is_countable_submanifold_measure_cover 1 1 [set x] set0.
  constructor; first exact:countable0.
  - by move=>S [].
  - rewrite /measure_almost_included bigcup_set0 setD0.
    exact:hausdorff_positive_degree_singleton_zero (ltn0Sn 0).
split; last exact hCover.
apply:(@federer_3_2_29 R 0 1 [set x]).2; by exists set0.
Qed.

(** Federer (1969), 3.2.30, p. 268: boundary regressions
    for actual zero exterior norm and an unbounded source, and
    a positive exterior degree above the target dimension. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanLinearJacobian EuclideanJacobianRank LinearRankUP LinearRankAtLeast ExteriorRankZero
  LinearExteriorMeasureImage LinearHausdorffMeasureImage ExteriorMeasure HausdorffMeasure MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_3_2_30_zero_map_unbounded]: regression
    for the singular case of Federer 3.2.30, p. 268.
    The actual zero map on the whole real line has zero first
    exterior norm and both image measures zero. The source is
    the whole unbounded line, without a finite-source premise. *)
Example federer_3_2_30_zero_map_unbounded (R:realType):
  euclidean_linear_jacobian 1 (0%R:Hom (R_n R 1) (R_n R 1))=0%R /\
  @exterior_diameter_measure R 1 1 ((0%R:Hom (R_n R 1) (R_n R 1)) @` setT)=0 /\
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 1)) 1
    ((0%R:Hom (R_n R 1) (R_n R 1)) @` setT)=0.
Proof.
pose L:=(0%R:Hom (R_n R 1) (R_n R 1)).
have hJ:euclidean_linear_jacobian 1 L=0%R.
  apply:(euclidean_linear_jacobian_zero_iff_singular L).2.
  move=>hInj.
  have hImages:L ([ffun _:'I_1=>(1%R:R)])=L (0%R:R_n R 1).
    by rewrite /L !hom_zeroE.
  have hEq:([ffun _:'I_1=>(1%R:R)])=(0%R:R_n R 1):=hInj _ _ hImages.
  have hh:=congr1 (fun v:R_n R 1=>v ord0) hEq.
  rewrite !ffunE in hh.
  change ((1%R:R)=(0%R:R)) in hh.
  by move:hh=>/eqP; rewrite oner_eq0.
have [hT hH]:=@federer_3_2_30 R 1 1 1 L setT (ltn0Sn 0).
rewrite hJ mul0e in hT.
rewrite hJ mulr0 mul0e in hH.
split; first exact hJ.
split.
- by apply/eqP; rewrite eq_le hT (measure_nonnegative (exterior_diameter_measure_is_measure R 1 1)).
- by apply/eqP; rewrite eq_le hH (measure_nonnegative (@hausdorff_measure_is_measure R _ 1)).
Qed.

(** Source for [federer_3_2_30_above_target_degree]: regression
    for the absence of degree bounds in Federer 3.2.30,
    p. 268. Every actual linear map R^2 -> R has zero
    second exterior norm, and the image of its whole unbounded
    source has zero exterior and Hausdorff two-measures. *)
Example federer_3_2_30_above_target_degree (R:realType)
    (L:Hom (R_n R 2) (R_n R 1)):
  euclidean_linear_jacobian 2 L=0%R /\
  @exterior_diameter_measure R 1 2 (L @` setT)=0 /\
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 1)) 2 (L @` setT)=0.
Proof.
have [r [hr hBound]]:=linear_rank_exists L (@coordinate_basisP R 1).
have hRank:~linear_rank_at_least L 2.
  move=>hh; have hTwo:(2<=r)%N:=(linear_rank_at_leastP 2 hr).1 hh.
  by have hFalse:=leq_trans hTwo hBound.
have hJ:euclidean_linear_jacobian 2 L=0%R:=euclidean_exterior_jacobian_rank_zero hRank.
have [hT hH]:=@federer_3_2_30 R 2 1 2 L setT (ltn0Sn 1).
rewrite hJ mul0e in hT.
rewrite hJ mulr0 mul0e in hH.
split; first exact hJ.
split.
- by apply/eqP; rewrite eq_le hT (measure_nonnegative (exterior_diameter_measure_is_measure R 1 2)).
- by apply/eqP; rewrite eq_le hH (measure_nonnegative (@hausdorff_measure_is_measure R _ 2)).
Qed.

(** Federer (1969), 3.2.31, pp. 268–269: original-domain
    regressions for a positive degree-zero atom and a positive-length
    identity source at the exact non-strict threshold one. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialMetricLipschitz
  RectifiablePartialFibreThreshold RectifiableSetUP RectifiableFiniteHausdorffMass
  HausdorffMeasure HausdorffCountingMeasure HausdorffClosedCoverAgreement
  MeasureUP MeasureBasic BorelRegularMeasureUP TopologicalBorel MetricDiameter MetricDiameterUP
  CompactSetDistanceProfile CompactMetricBounded MetricBoundedClosureLaws CoveringFamilyUP EuclideanLebesgueHaar EuclideanLebesgueDimensions EuclideanLebesgueBoxes EuclideanHausdorffLebesgue.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_3_2_31_positive_zero_atom]: regression
    for 3.2.31, pp. 268–269, at m=mu=0. The actual
    constant partial graph has one source atom, zero Lipschitz
    bound and a threshold set consisting of its target atom.
    That target has H^0 mass one, so it cannot be discarded
    as a null exceptional set or removed by a strict threshold. *)
Example federer_3_2_31_positive_zero_atom (R:realType) n v (a:R_n R n) (b:R_n R v):
  exists f:partial_function (R_n R n) (R_n R v),
    partial_function_domain f=[set a] /\
    @is_partial_metric_lipschitz_bound R (inner_metric_space (@euclidean_inner_productP R n))
      (inner_metric_space (@euclidean_inner_productP R v)) f 0%R /\
    [set y:R_n R v|1<=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) 0
      (partial_function_preimage f [set y])]=[set b] /\
    is_measure_m_rectifiable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R v)) 0) 0 [set b] /\
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R v)) 0 [set b]= 1.
Proof.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space (@euclidean_inner_productP R v).
pose f:=partial_function_source_restrict [set a] (partial_function_total (fun _:X=>b)).
have hDomain:partial_function_domain f=[set a].
  by rewrite /f partial_function_source_restrict_domain partial_function_total_domain setIT.
have hLip:@is_partial_metric_lipschitz_bound R X Y f 0%R.
  split; first exact:lexx.
  move=>x y c d [_ hc] [_ hd].
  change (b=c) in hc; change (b=d) in hd.
  by rewrite -hc -hd mdistxx mul0r.
have hSource:=@rectifiable_hausdorff_measure_rectifiable R 0 n [set a] (@finite_set1 _ a).
have hMeas:measure_measurable (@hausdorff_measure R X 0) [set a].
  apply:(borel_regular_borel_measurable (@hausdorff_measure_is_measure R X 0)
    (@hausdorff_measure_borel_regular R X 0)).
  apply:closed_borel_set; exact (compact_closed (@metric_hausdorff R X) (@compact_set1 X a)).
have hFormal:=@federer_3_2_31 R n v f 0%N 0%N 0%R 1%R (leqnn 0) ltr01.
have hRect:is_measure_m_rectifiable (@hausdorff_measure R Y 0) 0
    [set y:Y|1<=@hausdorff_measure R X 0 (partial_function_preimage f [set y])].
  apply:(hFormal _ _ hLip).2; by rewrite hDomain.
have hThreshold:[set y:Y|1<=@hausdorff_measure R X 0 (partial_function_preimage f [set y])]=[set b].
  apply/seteqP; split=>y.
  - move=>hy; apply/eqP; apply:contrapT=>hne.
    have hEmpty:partial_function_preimage f [set y]=set0.
      apply/seteqP; split=>x; last by [].
      move=>[z [[hx hbz] hzy]].
      change (b=z) in hbz; change (z=y) in hzy.
      have he:b=y:=eq_trans hbz hzy.
      by move:hne; rewrite -he eqxx.
    change (is_true (1<=@hausdorff_measure R X 0 (partial_function_preimage f [set y]))) in hy.
    by move:hy; rewrite hEmpty (measure_empty (@hausdorff_measure_is_measure R X 0)) lee_fin ler10.
  - move=>->.
    have hFibre:partial_function_preimage f [set b]=[set a].
      apply/seteqP; split=>x.
      + by move=>[z [[hx _] _]].
      + move=>hx; exists b; split; first by split.
        reflexivity.
    change (is_true (1<=@hausdorff_measure R X 0 (partial_function_preimage f [set b]))).
    by rewrite hFibre hausdorff_zero_singleton.
exists f; split; first exact hDomain.
split; first exact hLip.
split; first exact hThreshold.
split; last exact:hausdorff_zero_singleton.
by rewrite -hThreshold.
Qed.

(** Source for [federer_3_2_31_identity_unit_interval]: regression
    for the positive-degree case of 3.2.31, pp. 268–269.
    The identity on the closed unit interval has threshold-one
    set exactly that interval. It has positive H^1 mass and
    is finite (H^1,1)-rectifiable, testing the main proof and
    exact non-strict threshold on the original partial domain. *)
Example federer_3_2_31_identity_unit_interval (R:realType):
  let Q:set (R_n R 1):=[set x|forall i,(0<=x i<= 1)%R] in
  exists f:partial_function (R_n R 1) (R_n R 1),
    partial_function_domain f=Q /\
    @is_partial_metric_lipschitz_bound R (inner_metric_space (@euclidean_inner_productP R 1))
      (inner_metric_space (@euclidean_inner_productP R 1)) f 1%R /\
    [set y:R_n R 1|1<=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 1)) 0
      (partial_function_preimage f [set y])]=Q /\
    is_measure_m_rectifiable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 1)) 1) 1 Q /\
    1<=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 1)) 1 Q.
Proof.
move=>Q.
pose X:=inner_metric_space (@euclidean_inner_productP R 1).
pose f:=partial_function_source_restrict Q (partial_function_total (fun x:X=>x)).
have hDomain:partial_function_domain f=Q.
  by rewrite /f partial_function_source_restrict_domain partial_function_total_domain setIT.
have hLip:@is_partial_metric_lipschitz_bound R X X f 1%R.
  split; first exact:ler01.
  move=>x y a b [_ hxa] [_ hyb].
  change (x=a) in hxa; change (y=b) in hyb.
  by rewrite -hxa -hyb mul1r.
have hCompact:@compact X Q.
  exact (@euclidean_closed_box_compact R 1%N (fun _:'I_1=>0%R) (fun _:'I_1=>1%R)).
have hNonempty:Q!=set0.
  exists (0%R:X)=>i; by rewrite ffunE ler01 lexx.
pose CQ:compact_metric_set X:=exist _ Q (mem_set (conj hCompact hNonempty)).
have hBounded:@metric_set_bounded R X Q.
  exact (@metric_bounded_subset R X Q Q (fun x (hx:Q x)=>hx) (compact_metric_diameter_finite CQ)).
have hGenuine:@is_m_rectifiable R X 1 Q.
  exists f; split; first by rewrite hDomain.
  split; first by exists 1%R.
  apply/seteqP; split=>y.
  - by move=>[x [hx hxy]]; rewrite -hxy.
  - move=>hy; exists y; by split.
have hSource:=@rectifiable_hausdorff_measure_rectifiable R 1 1 Q hGenuine.
have hMeas:measure_measurable (@hausdorff_measure R X 1) Q.
  apply:(borel_regular_borel_measurable (@hausdorff_measure_is_measure R X 1)
    (@hausdorff_measure_borel_regular R X 1)).
  apply:closed_borel_set; exact (compact_closed (@metric_hausdorff R X) hCompact).
have hFormal:=@federer_3_2_31 R 1 1 f 1%N 1%N 1%R 1%R (leqnn 1) ltr01.
have hRect:is_measure_m_rectifiable (@hausdorff_measure R X 1) 1
    [set y:X|1<=@hausdorff_measure R X 0 (partial_function_preimage f [set y])].
  apply:(hFormal _ _ hLip).2; by rewrite hDomain.
have hThreshold:[set y:X|1<=@hausdorff_measure R X 0 (partial_function_preimage f [set y])]=Q.
  apply/seteqP; split=>y.
  - move=>hy; case:(pselect (Q y))=>hQ; first exact hQ.
    have hEmpty:partial_function_preimage f [set y]=set0.
      apply/seteqP; split=>x; last by [].
      move=>[z [[hx hxz] hzy]].
      change (x=z) in hxz; change (z=y) in hzy.
      apply:hQ; by rewrite -(eq_trans hxz hzy).
    change (is_true (1<=@hausdorff_measure R X 0 (partial_function_preimage f [set y]))) in hy.
    by move:hy; rewrite hEmpty (measure_empty (@hausdorff_measure_is_measure R X 0)) lee_fin ler10.
  - move=>hy.
    have hFibre:partial_function_preimage f [set y]=[set y].
      apply/seteqP; split=>x.
      + move=>[z [[hx hxz] hzy]].
        change (x=z) in hxz; change (z=y) in hzy; exact (eq_trans hxz hzy).
      + move=>->; exists y; split; first by split.
        reflexivity.
    change (is_true (1<=@hausdorff_measure R X 0 (partial_function_preimage f [set y]))).
    by rewrite hFibre hausdorff_zero_singleton.
have hPositive:1<=@hausdorff_measure R X 1 Q.
  pose A:set X:=[set x|forall i,(0<x i<1)%R].
  have hMass:@hausdorff_measure R X 1 A= 1.
    by rewrite (euclidean_hausdorff_spherical_lebesgue A).1 euclidean_unit_cube.
  rewrite -hMass; apply:(measure_mono (@hausdorff_measure_is_measure R X 1))=>x hx i.
  have /andP [hx0 hx1]:=hx i; apply/andP; split; exact:ltW.
exists f; split; first exact hDomain.
split; first exact hLip.
split; first exact hThreshold.
split; last exact hPositive.
by rewrite -hThreshold.
Qed.

(** Federer (1969), 3.2.32, pp. 269–270:
    positive-atom and positive-length whole-corollary regressions. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  PartialFunctionUP PartialFunctionBasic PartialMetricLipschitz RectifiableSetUP
  RectifiableFiniteHausdorffMass HausdorffMeasure HausdorffCountingMeasure HausdorffZeroNullEmpty
  HausdorffZeroPositiveThreshold HausdorffClosedCoverAgreement MeasureUP MeasureBasic BorelRegularMeasureUP
  TopologicalBorel EuclideanLebesgueHaar EuclideanLebesgueBoxes RectifiablePositiveFibreCoareaUP RectifiablePositiveFibreCoarea.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_3_2_32_positive_zero_atom]: regression for
    the entire corollary 3.2.32, p. 269, at m=mu=0.
    The same actual singleton partial graph used for 3.2.31
    has positive unit source and target atoms and zero Lipschitz
    bound. The null rank exception is empty, forcing the actual
    image-dimension conclusion at its source atom. Thus a null or
    empty exceptional-set argument cannot hide the degree-zero case. *)
Example federer_3_2_32_positive_zero_atom (R:realType) n v (a:R_n R n) (b:R_n R v):
  exists f:partial_function (R_n R n) (R_n R v),
    partial_function_domain f=[set a] /\
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) 0 (partial_function_domain f)= 1 /\
    positive_partial_fibre_locus 0 0 f=[set b] /\
    is_rectifiable_positive_fibre_coarea 0 0 f /\
    partial_approximate_image_dimension_locus 0 0 f a.
Proof.
have [f [hDomain [hLip [hThreshold [hRectB hMassB]]]]]:=
  @federer_3_2_31_positive_zero_atom R n v a b.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=@hausdorff_measure R X 0.
have hH:=@hausdorff_measure_is_measure R X 0.
have hSource:=@rectifiable_hausdorff_measure_rectifiable R 0 n [set a] (@finite_set1 _ a).
have hMeas:measure_measurable H [set a].
  apply:(borel_regular_borel_measurable hH (@hausdorff_measure_borel_regular R X 0)).
  apply:closed_borel_set; exact:(compact_closed (@metric_hausdorff R X) (@compact_set1 X a)).
have hRect:is_measure_m_rectifiable H 0 (partial_function_domain f) by rewrite hDomain.
have hDomMeas:measure_measurable H (partial_function_domain f) by rewrite hDomain.
have hFormal:=@federer_3_2_32 R n v 0 0 f 0%R (leqnn 0) hRect hDomMeas hLip.
have hY:positive_partial_fibre_locus 0 0 f=[set b].
  have hEqual:positive_partial_fibre_locus 0 0 f=
      [set y|1<=H (partial_function_preimage f [set y])].
    apply:funext=>y.
    change (is_true (0<H (partial_function_preimage f [set y]))=
      is_true (1<=H (partial_function_preimage f [set y]))).
    by rewrite hausdorff_zero_positive_iff_unit_threshold.
  exact:(eq_trans hEqual hThreshold).
have hFibreMass:0<H (partial_function_preimage f [set b]).
  have hb:(positive_partial_fibre_locus 0 0 f) b by rewrite hY.
  exact hb.
have hFibreNonempty:exists x,partial_function_preimage f [set b] x.
  case:(pselect (exists x,partial_function_preimage f [set b] x))=>h; first exact h.
  have hEmpty:partial_function_preimage f [set b]=set0.
    apply/seteqP; split=>[x hx|x []]; exfalso; apply:h; by exists x.
  change (is_true (0<@hausdorff_measure R X 0 (partial_function_preimage f [set b]))) in hFibreMass.
  by rewrite hEmpty (measure_empty hH) ltxx in hFibreMass.
have [x [y [hxy hy]]]:=hFibreNonempty.
have hx:partial_function_domain f x by exists y.
have hxa:x=a by rewrite hDomain in hx.
have hAy:partial_function_preimage f (positive_partial_fibre_locus 0 0 f) a.
  exists y; split; first by rewrite -hxa.
  rewrite hY; exact hy.
have hEmpty:=hausdorff_zero_null_set_empty (rectifiable_positive_fibre_rank_law hFormal).
have hRank:partial_approximate_image_dimension_locus 0 0 f a.
  apply:contrapT=>hn.
  have hBad:(partial_function_preimage f (positive_partial_fibre_locus 0 0 f) `\`
    partial_approximate_image_dimension_locus 0 0 f) a by split.
  by rewrite hEmpty in hBad.
exists f; split; first exact hDomain.
split; first by rewrite hDomain hausdorff_zero_singleton.
split; first exact hY; by split.
Qed.

(** Source for [federer_3_2_32_positive_length_source]: regression for
    the positive-degree corollary 3.2.32, pp. 269–270.
    The original partial identity supplied by the unit-interval
    regression has positive H^1 source mass. Its positive-fibre
    locus is exactly the interval, and both rank and integral
    conclusions hold with no target or derivative-field premise. *)
Example federer_3_2_32_positive_length_source (R:realType):
  let Q:set (R_n R 1):=[set x|forall i,(0<=x i<= 1)%R] in
  exists f:partial_function (R_n R 1) (R_n R 1),
    partial_function_domain f=Q /\positive_partial_fibre_locus 1 1 f=Q /\
    1<=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 1)) 1 (partial_function_domain f) /\
    is_rectifiable_positive_fibre_coarea 1 1 f.
Proof.
move=>Q.
have [f [hDomain [hLip [hThreshold [hRectQ hPositive]]]]]:=@federer_3_2_31_identity_unit_interval R.
pose X:=inner_metric_space (@euclidean_inner_productP R 1).
pose H:=@hausdorff_measure R X 1.
have hMeas:measure_measurable H Q.
  apply:(borel_regular_borel_measurable (@hausdorff_measure_is_measure R X 1)
    (@hausdorff_measure_borel_regular R X 1)).
  apply:closed_borel_set; apply:(compact_closed (@metric_hausdorff R X)).
  exact:(@euclidean_closed_box_compact R 1%N (fun _:'I_1=>0%R) (fun _:'I_1=>1%R)).
have hRect:is_measure_m_rectifiable H 1 (partial_function_domain f) by rewrite hDomain.
have hDomMeas:measure_measurable H (partial_function_domain f) by rewrite hDomain.
have hFormal:=@federer_3_2_32 R 1 1 1 1 f 1%R (leqnn 1) hRect hDomMeas hLip.
have hY:positive_partial_fibre_locus 1 1 f=Q.
  have hEqual:positive_partial_fibre_locus 1 1 f=
      [set y|1<=@hausdorff_measure R X 0 (partial_function_preimage f [set y])].
    apply:funext=>y.
    change (is_true (0<@hausdorff_measure R X 0 (partial_function_preimage f [set y]))=
      is_true (1<=@hausdorff_measure R X 0 (partial_function_preimage f [set y]))).
    by rewrite hausdorff_zero_positive_iff_unit_threshold.
  exact:(eq_trans hEqual hThreshold).
exists f; split; first exact hDomain.
split; first exact hY; split; last exact hFormal.
by rewrite hDomain.
Qed.

(** Public boundary regressions for the smooth example in
    Federer (1969), 3.2.33, p. 270. These retain positive
    source mass and the actual original partial Jacobian. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanOpenUnitCube
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialFunctionPreimages
  MeasureRestriction HausdorffMeasure MeasureSubsetIntegral MeasureApproximateJacobian RectifiablePositiveFibreCoareaUP
  SmoothCoareaRemainderExampleUP SmoothCoareaRemainderExampleExistence ScalarCylinderMapUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [smooth_coarea_zero_degree_positive_length_example]:
    the explicit mu=0 convention of Federer 3.2.33,
    p. 270. A smooth scalar map on the unit interval
    satisfies 3.2.32 and has no positive-length fibre,
    yet its exact rank-zero source has positive length
    and the original degree-zero Jacobian integral equals
    that positive length. Neither an empty source nor a
    zero-mass stand-in can satisfy this regression. *)
Example smooth_coarea_zero_degree_positive_length_example (R:realType):
  exists F:R_n R 1->R_n R 1,
    let f:=partial_function_source_restrict (@euclidean_open_unit_cube R 1) (partial_function_total F) in
    let X:=partial_approximate_image_dimension_locus 1 0 f in
    let H:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 1)) 1 in
    is_rectifiable_positive_fibre_coarea 1 0 f /\positive_partial_fibre_locus 1 0 f=set0 /\
    (0<H X)%E /\is_measure_subset_integral H X
      (extended_measure_approximate_jacobian (measure_restrict H (partial_function_domain f)) 1 0 f) (H X).
Proof.
have [F hF]:=@federer_3_2_33_smooth R 1 0 (erefl true).
exists F; split; first exact:(smooth_remainder_example_coarea hF).
split; first exact:(smooth_remainder_example_empty_fibres hF).
split; first exact:(smooth_remainder_example_positive_source hF).
have hI:=smooth_remainder_example_integral hF.
by rewrite (smooth_remainder_example_empty_fibres hF) partial_function_preimage_empty setD0 in hI.
Qed.

(** Source for [smooth_coarea_singleton_fibre_positive_rank_example]:
    the k=0 and positive-mu boundary of Federer 3.2.33,
    p. 270. The actual two-coordinate map preserves its
    first coordinate and has positive area in its rank-one
    source, but every required length fibre is null. The
    original degree-one approximate Jacobian integral remains
    strictly positive, catching a missing endpoint or an
    unjustified inference from the empty positive-fibre set. *)
Example smooth_coarea_singleton_fibre_positive_rank_example (R:realType):
  exists (g:R->R) (F:R_n R 2->R_n R 2),
    is_scalar_cylinder_map (mu:=1) (k:=0) g F /\
    @is_smooth_coarea_remainder_example R 1 2 F /\
    forall x,F x (lshift 1 (ord0:'I_1))=x (lshift 0 (lshift 1 (ord0:'I_1))).
Proof.
have [a [b [phi [psi [g [F [hPhi [hFamily [hSeries [hPrimitive [hF hExample]]]]]]]]]]]:=
  @smooth_coarea_remainder_example_exists R 1 0.
exists g,F; split; first exact hF.
split; first exact hExample.
move=>x; exact:(scalar_cylinder_first_coordinates hF x ord0).
Qed.

(** Boundary regressions for Federer (1969), 3.2.34,
    p. 271: positive-dimensional source with H^0
    fibres, and an actual unbounded nonconvex closed set. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology num_normedtype lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanOneCoordinate EuclideanOneNormDifferential MetricSetDistanceUP MetricSetDistanceBasic
  MetricSetDistanceSealed MetricSetDistanceContinuity EuclideanDistanceStripCoarea
  ClosedSetDistanceCoarea EuclideanOpenPositiveMass HausdorffMeasure EuclideanLebesgueDimensions LebesgueScalarMeasure
  PartialFunctionUP PartialFunctionBasic RealMetricBackground RealOpenIntervals MeasureSubsetIntegral ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [closed_distance_line_counting_fibres_example]:
    the n=1 boundary of Federer 3.2.34, p. 271.
    The actual distance to {0} is the absolute
    Euclidean norm; its whole H^0 level fibres
    occur in the scalar integral. This invokes the
    equal-dimension area boundary of coarea and does
    not replace the source by a null set. *)
Example closed_distance_line_counting_fibres_example (R:realType):
  (0<@euclidean_lebesgue_measure R 1
    [set x|(0<inner_norm (@euclidean_inner_productP R 1) x<2)%R])%E /\
  is_measure_subset_integral (@lebesgue_scalar_measure R) (real_open_interval (0:R) 2)
    (partial_function_total (fun t:R=>(@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R 1)) 0
      [set x|inner_norm (@euclidean_inner_productP R 1) x=t]:extended_real_line R)))
    (@euclidean_lebesgue_measure R 1
      [set x|0<inner_norm (@euclidean_inner_productP R 1) x<2]).
Proof.
pose E:=inner_metric_space (@euclidean_inner_productP R 1).
pose N:=inner_norm (@euclidean_inner_productP R 1).
have hClosed:closed [set (0:E)].
  apply:accessible_closed_set1; apply:hausdorff_accessible; exact:metric_hausdorff.
have hNonempty:([set (0:E)] :set E)!=set0 by exists 0.
have hDistance:is_metric_set_distance [set (0:E)] N.
  constructor.
  - move=>x s hs; have he:s=0:=hs.
    by rewrite he inner_metric_distanceE subr0.
  - move=>x r hb; have hh:=hb 0 (erefl 0).
    by rewrite inner_metric_distanceE subr0 in hh.
split.
- apply:(euclidean_open_positive_mass (a:=euclidean_one_embed (1:R))
    (@euclidean_distance_strip_open R 1 [set (0:E)] N 0 2 hDistance)).
  change (is_true (0<inner_norm (@euclidean_inner_productP R 1)
    (euclidean_one_embed (1:R))<2)).
  by rewrite euclidean_one_norm_coordinate /euclidean_one_embed ffunE normr1 ltr01 ltr1n.
- exact:(@federer_3_2_34 R 1 [set (0:E)] N 0 2
  (erefl true) hClosed hNonempty hDistance (ltac:(by rewrite lexx ltr0n))).
Qed.

(** Source for [closed_distance_two_rays_example]: the
    lack of any boundedness or convexity hypothesis
    in Federer 3.2.34, p. 271. S is
    the actual union of the two rays (-infinity,0]
    and [2,infinity) in the Euclidean line. Its
    opaque distance has value one at the midpoint,
    and the whole scalar strip formula applies with
    the printed endpoint a=0 and H^0 fibres. *)
Example closed_distance_two_rays_example (R:realType):
  let E:=inner_metric_space (@euclidean_inner_productP R 1) in
  let S:set E:=[set x|euclidean_one_project x<=0] `|`
    [set x|2<=euclidean_one_project x] in
  exists d:E->R,is_metric_set_distance S d /\d (euclidean_one_embed (1:R))= 1 /\
    is_measure_subset_integral (@lebesgue_scalar_measure R) (real_open_interval (0:R) 2)
      (partial_function_total (fun t:R=>(@hausdorff_measure R E 0 [set x|d x=t]
        :extended_real_line R))) (@euclidean_lebesgue_measure R 1 [set x|0<d x<2]).
Proof.
move=>E S.
have hClosed:closed S.
  apply:closedU.
  - change (closed ((@euclidean_one_project R) @^-1` [set t:real_line_metric R|t<=0])).
    apply:preimage_closed; last exact:closed_le.
    by move=>x _; exact:euclidean_one_project_continuous.
  - change (closed ((@euclidean_one_project R) @^-1` [set t:real_line_metric R|2<=t])).
    apply:preimage_closed; last exact:closed_ge.
    by move=>x _; exact:euclidean_one_project_continuous.
have hNonempty:S!=set0.
  exists (euclidean_one_embed (0:R)); left.
  change (is_true (euclidean_one_project (euclidean_one_embed (0:R))<=0)).
  by rewrite euclidean_one_embedK.
pose d:=MetricSetDistance.value hNonempty.
have hD:=MetricSetDistance.laws hNonempty.
exists d; split; first exact hD; split.
- apply/eqP; rewrite eq_le; apply/andP; split.
  + have hs:S (euclidean_one_embed (0:R)).
      left; change (is_true (euclidean_one_project (euclidean_one_embed (0:R))<=0)).
      by rewrite euclidean_one_embedK.
    have hh:=metric_set_distance_lower hD (euclidean_one_embed (1:R)) hs.
    by rewrite inner_metric_distanceE euclidean_one_norm_coordinate
      /euclidean_one_embed !ffunE subr0 normr1 in hh.
  + apply:(metric_set_distance_greatest hD).
    move=>s hs; rewrite inner_metric_distanceE euclidean_one_norm_coordinate
      /euclidean_one_embed !ffunE.
    change (is_true (1<=`|1-euclidean_one_project s|)).
    case:hs=>hs.
    * change (is_true (euclidean_one_project s<=0)) in hs.
      have hPos:0<=1-euclidean_one_project s by lra.
      by rewrite ger0_norm //; lra.
    * change (is_true (2<=euclidean_one_project s)) in hs.
      have hNeg:1-euclidean_one_project s<=0 by lra.
      rewrite ler0_norm // opprB; lra.
- exact:(@federer_3_2_34 R 1 S d 0 2 (erefl true) hClosed hNonempty hD
    (ltac:(by rewrite lexx ltr0n))).
Qed.

(** Federer (1969), 3.2.35, pp. 271--272:
    actual positive-atom, lower-dimensional source
    and two-endpoint boundary regressions. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm InnerMetric
  InnerConvex CoveringFamilyUP MetricDiameterMaps MetricSetDistanceUP MetricSetDistanceSealed
  EuclideanNormSetDistance SteinerTubePolynomial ConvexSteinerTubeFormula ZeroDegreeIntegralGauge
  EuclideanUnitBallProjection EuclideanBallVolume FullDimensionIntegralGauge EuclideanLebesgueDimensions
  EuclideanHausdorffLebesgue HausdorffMeasure HausdorffCountingMeasure HausdorffCountableNull
  CountingInjectionBound RectifiableSetUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [steiner_zero_dimension_positive_atom_example]:
    the empty-product boundary of the Steiner
    polynomial in Federer 3.2.35, p. 271.
    The actual source point has positive H^0
    mass one, and every actual positive tube
    has volume one. The complete dimension
    theorem is invoked with its original laws. *)
Example steiner_zero_dimension_positive_atom_example (R:realType):
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 0)) 0 [set 0]= 1%E /\
  forall r:R,0<r ->euclidean_lebesgue_measure 0
    [set x|inner_norm (@euclidean_inner_productP R 0) x<r]= 1%E.
Proof.
pose E:=inner_metric_space (@euclidean_inner_productP R 0).
pose S:set E:=[set 0].
have hNonempty:S!=set0 by exists 0.
have hConvex:is_inner_convex S.
  move=>x y -> -> t _ _; by rewrite -scalerDl subrK scaler0.
have hBound:metric_set_bounded S.
  by rewrite /S /metric_set_bounded extended_metric_diameter_singleton; exact:ltry.
have hFormula:=@convex_steiner_tube_formula R 0 S (inner_norm (@euclidean_inner_productP R 0))
  hNonempty hConvex hBound (@euclidean_norm_set_distance R 0).
split.
- by rewrite hausdorff_zero_counting_measure counting_measure_singleton_value.
- move=>r hr; have hTube:=hFormula r hr.
  by rewrite (@steiner_tube_polynomial_zero_dimension R S r hNonempty) in hTube.
Qed.

(** Source for [steiner_line_point_tube_example]: the
    actual lower-dimensional source {0} in R
    for Federer 3.2.35, p. 271.
    The complete numbered theorem gives the
    original tube length 2r at every positive
    radius; its positive mass prevents a
    zero-measure or empty-tube interpretation. *)
Example steiner_line_point_tube_example (R:realType) (r:R):
  0<r ->euclidean_lebesgue_measure 1
      [set x|(inner_norm (@euclidean_inner_productP R 1) x<r)%R]=(2*r)%:E /\
    (0<euclidean_lebesgue_measure 1
      [set x|(inner_norm (@euclidean_inner_productP R 1) x<r)%R])%E.
Proof.
move=>hr.
pose E:=inner_metric_space (@euclidean_inner_productP R 1).
pose S:set E:=[set 0].
have hNonempty:S!=set0 by exists 0.
have hConvex:is_inner_convex S.
  move=>x y -> -> t _ _; by rewrite -scalerDl subrK scaler0.
have hBound:metric_set_bounded S.
  by rewrite /S /metric_set_bounded extended_metric_diameter_singleton; exact:ltry.
have hMass:euclidean_lebesgue_measure 1 S= 0%E.
  rewrite -(euclidean_hausdorff_spherical_lebesgue S).1.
  exact:(@hausdorff_positive_degree_singleton_zero R E 1 0 (erefl true)).
have hFormula:=(@federer_3_2_35 R 0 S (inner_norm (@euclidean_inner_productP R 1))
  hNonempty hConvex hBound (@euclidean_norm_set_distance R 1)).1.
have hTube:=hFormula r hr.
rewrite /steiner_tube_polynomial !big_ord_recr !big_ord0 /= ?add0e ?add0r
  (@zero_degree_integral_geometric_gauge R 1 _ S hNonempty)
  (@equal_dimension_integral_geometric_gauge R 1 _ 1 S (lexx 1)) hMass
  euclidean_unit_ball_volume0 euclidean_unit_ball_volume1 expr0 expr1 mulr1
  mul1e mul0e adde0 in hTube.
have hTubeValue:euclidean_lebesgue_measure 1
    [set x|(inner_norm (@euclidean_inner_productP R 1) x<r)%R]=(2*r)%:E:=hTube.
split; first exact hTubeValue.
by rewrite hTubeValue lte_fin mulr_gt0 // ltr0n.
Qed.

(** Source for [steiner_cauchy_line_boundary_example]: the
    actual open unit ball in the Euclidean
    line for the second assertion of Federer
    3.2.35, p. 271. The whole numbered
    theorem proves genuine finite degree-zero
    rectifiability and exactly two H^0 boundary
    atoms, with all original body hypotheses
    and actual distance laws discharged. *)
Example steiner_cauchy_line_boundary_example (R:realType):
  let B:set (inner_metric_space (@euclidean_inner_productP R 1)):=
    [set x|inner_norm (@euclidean_inner_productP R 1) x<1] in
  is_m_rectifiable 0 (closure B `\` interior B) /\
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 1)) 0 (closure B `\` interior B)=(2:R)%:E.
Proof.
move=>B.
have [hNonempty [hOpen [hConvex hBound]]]:=euclidean_unit_ball_convex_bounded R 1.
pose d:=MetricSetDistance.value hNonempty.
have hWhole:=@federer_3_2_35 R 0 B d hNonempty hConvex hBound (MetricSetDistance.laws hNonempty).
have [hRect hMass]:=hWhole.2 hOpen.
rewrite (@zero_degree_integral_geometric_gauge R 1 _ B hNonempty) mule1 in hMass.
by split.
Qed.

(** Federer (1969), 3.2.36, pp. 272--273:
    concrete lower-dimensional, atomic and zero-section regressions. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology ring.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  CoordinateProjection OrthonormalFamilies EuclideanBoxUP CoordinateEdgeBoxGeometry
  ElementarySymmetricCoefficientsUP RectangularBoxIntrinsicVolumes IntegralGeometricGauge SteinerTubePolynomial
  ConvexIntegralGeometricIsometricEmbedding IntegralGeometricMeasure EuclideanOneCoordinate
  WeightedRadialSectionIntegral EuclideanBallVolume RealOpenIntervals LebesgueScalarMeasure
  MeasureSubsetIntegral SummableRealFunctionUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rectangular_box_zero_width_coefficients_example]: the
    whole box formula of Federer 3.2.36, p. 273, tested on
    the actual two-dimensional coordinate box of widths 2 and 0.
    Its independent edge polynomial is 1+2t; all three actual
    coefficients are therefore 1,2,0. The positive first coefficient
    and degree-zero atom prevent a vacuous zero-mass interpretation. *)
Example rectangular_box_zero_width_coefficients_example (R:realType):
  forall j:'I_3,@integral_geometric_gauge R 2 j (steiner_dimension_guard j) 1
    (coordinate_edge_box (fun i:'I_2=>if i==ord0 then 2 else 0))=
    (if ((j:nat)==0)%N then 1 else if ((j:nat)==1)%N then 2 else 0)%R%:E.
Proof.
pose w:=fun i:'I_2=>if i==ord0 then (2:R) else 0.
pose e:=fun j:'I_3=>if ((j:nat)==0)%N then (1:R) else if ((j:nat)==1)%N then 2 else 0.
have hc:forall i,0<=w i.
  move=>i; rewrite /w; case:ifP=>h; [exact:(@ler0n R 2)|exact:lexx].
have hBox:@is_euclidean_rectangular_box R 2 0 (@coordinate_basis R 2) w (coordinate_edge_box w).
  constructor.
  - by move=>i j; rewrite euclidean_inner_basis /coordinate_basis ffunE eq_sym.
  - exact hc.
  - move=>x; split=>hx i.
    + by rewrite subr0 euclidean_inner_basis; exact:hx.
    + have h:=hx i; by rewrite subr0 euclidean_inner_basis in h.
have hE:is_elementary_symmetric_coefficients w e.
  move=>t; rewrite !big_ord_recr !big_ord0 /w /e /=; ring.
move=>j; exact:(@rectangular_box_intrinsic_volume_coefficient R 2 0 (@coordinate_basis R 2) w
  (coordinate_edge_box w) e hBox hE j).
Qed.

(** Source for [isometric_embedding_zero_dimension_positive_atom_example]:
    the actual R^0-to-line embedding in the Q_1 assertion of
    Federer 3.2.36, p. 273. Its source atom has actual Q^0
    mass one by 3.2.26, p. 261; the full arbitrary-set embedding
    theorem transports that positive atom. No singleton is discarded
    as null and no positive ambient or intrinsic dimension is assumed. *)
Example isometric_embedding_zero_dimension_positive_atom_example (R:realType):
  @convex_integral_geometric_measure R 0 0 (leqnn 0) 1
    [set (0:inner_metric_space (@euclidean_inner_productP R 0))]= 1%E /\
  @convex_integral_geometric_measure R 1 0 (leq0n 1) 1
    ((fun _:inner_metric_space (@euclidean_inner_productP R 0)=>
      (0:inner_metric_space (@euclidean_inner_productP R 1))) @`
      [set (0:inner_metric_space (@euclidean_inner_productP R 0))])= 1%E.
Proof.
pose X:=inner_metric_space (@euclidean_inner_productP R 0).
pose Y:=inner_metric_space (@euclidean_inner_productP R 1).
pose f:X->Y:=fun _=>0.
have hMetric (x y:X):mdist (f x) (f y)=mdist x y.
  by rewrite /f (coordinate_zero x) (coordinate_zero y) !mdistxx.
have [_ [_ [_ hAtoms]]]:=@zero_degree_geometric_measure_atom_regression R 0 (0:X).
have [hSource _]:=hAtoms 1%E (lexx 1%E).
rewrite -(bool_irrelevance (leqnn 0) (leq0n 0)) in hSource.
have hImage:=@convex_integral_geometric_isometric_embedding R 0 1 0 (leqnn 0) (leq0n 1) f hMetric [set (0:X)].
split; first exact hSource.
by rewrite hImage hSource.
Qed.

(** Source for [radial_section_zero_degree_endpoint_example]: the
    xi=1, eta=0 radius term in Federer 3.2.36, p. 273.
    The actual scalar integral equals the strictly positive alpha(1),
    with both positive H^0 sphere atoms and the nonzero endpoint
    section retained before the proved scalar null-set removal. *)
Example radial_section_zero_degree_endpoint_example (R:realType):
  is_measure_subset_integral (@lebesgue_scalar_measure R) (real_open_interval 0 1)
    (real_total_integrand (fun _:R=>euclidean_unit_ball_volume R 1))
    (euclidean_unit_ball_volume R 1)%:E /\0<euclidean_unit_ball_volume R 1.
Proof.
have h:=@weighted_radial_section_integral R 1 0 1 (ltnSn 0) (ltr01).
rewrite euclidean_unit_ball_volume0 ?mul1r ?mulr1 ?expr0 ?expr1 ?expr1n in h.
have hKernel:(fun s:R=>euclidean_unit_ball_volume R 1*s^+(1-1)*Num.sqrt (1-s^+2)^+0)=
    (fun _:R=>euclidean_unit_ball_volume R 1).
  apply:funext=>s; by rewrite subnn !expr0 !mulr1.
rewrite hKernel in h.
split; first exact h.
exact:(euclidean_unit_ball_volumeE R 1).2.
Qed.

(** Federer (1969), 3.2.37, pp. 273--274: positive
    degree-zero atoms, countable dense null sources with infinite
    tube contents, and positive-degree finite sources. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  MinkowskiContents MinkowskiZeroCounting MinkowskiNonmeasure MinkowskiContentTheorem
  CountingMeasure NonnegativeSumSupport MeasureUP HausdorffMeasure HausdorffCountableNull.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [minkowski_zero_dimension_positive_atom_example]:
    the actual ambient-zero atom in the definitions of Federer
    3.2.37, p. 273, and the necessary degree-zero qualification
    to p. 274. Both contents of the unique vector are one and
    both entire degree-zero content functions are measures. *)
Example minkowski_zero_dimension_positive_atom_example (R:realType):
  let x:inner_metric_space (@euclidean_inner_productP R 0):=0%R in
  upper_minkowski_content 0 [set x]= 1 /\lower_minkowski_content 0 [set x]= 1 /\
    is_measure (@upper_minkowski_content R 0 0) /\is_measure (@lower_minkowski_content R 0 0).
Proof.
move=>x.
have hCount:@counting_measure R (inner_metric_space (@euclidean_inner_productP R 0)) [set x]= 1.
  rewrite counting_measure_sum nonnegative_sum_singleton; first by [].
  by rewrite lee_fin ler01.
have [hUpper hLower]:=@zero_minkowski_contents_counting R 0 [set x].
rewrite hCount in hUpper hLower.
have [hMeasureUpper hMeasureLower]:=@zero_minkowski_contents_are_measures R 0.
by split=>//; split=>//; split.
Qed.

(** Source for [minkowski_countable_dense_null_line_example]:
    the non-measure assertion of Federer 3.2.37, p. 274,
    tested in top degree one, so the normal coordinate block is
    zero. An actual countable dense original source has zero
    H^1 mass but infinite upper and lower contents. *)
Example minkowski_countable_dense_null_line_example (R:realType):
  exists D:set (inner_metric_space (@euclidean_inner_productP R 1)),
    [/\ countable D,dense D,
      @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 1)) 1 D=0,
      upper_minkowski_content 1 D= +oo & lower_minkowski_content 1 D= +oo].
Proof.
have [D [hCountable hDense hUpper hLower _]]:=
  @positive_minkowski_contents_not_measures R 1 1 (ltnSn 0) (leqnn 1).
exists D; split=>//.
exact:(@hausdorff_positive_degree_countable_zero R
  (inner_metric_space (@euclidean_inner_productP R 1)) 1 D (ltnSn 0) hCountable).
Qed.

(** Source for [minkowski_positive_degree_line_point_example]:
    the actual line origin has zero positive-degree upper and
    lower contents, Federer 3.2.37, pp. 273--274. This retains
    the full-dimension case m=n= 1 rather than requiring m<n. *)
Example minkowski_positive_degree_line_point_example (R:realType):
  let x:inner_metric_space (@euclidean_inner_productP R 1):=0%R in
  upper_minkowski_content 1 [set x]=0 /\lower_minkowski_content 1 [set x]=0.
Proof.
move=>x; exact:(@positive_minkowski_singletons_zero R 1 1 x (ltnSn 0) (leqnn 1)).
Qed.

(** Federer (1969), 3.2.38, pp. 274--275: actual
    zero-map, positive source atom and original empty-source regressions. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLinearJacobian
  EuclideanJacobianMeasurable EuclideanJacobianRank EuclideanJacobianUpperBound Jacobian
  JacobianDensityMeasure AreaCriticalImageNull PartialFunctionUP MeasureSubsetIntegral
  CompactLipschitzImageMinkowski MissingSteinerConstantCounterexample ZeroSourceMinkowskiImage
  MinkowskiContents MinkowskiContentsBasic MinkowskiZeroCounting CountingMeasure NonnegativeSumSupport
  EuclideanLebesgueDimensions EuclideanLebesgueBoxes LipschitzUP MeasureUP MeasureBasic MeasureSplit TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_minkowski_constant_map_correction_example]:
    the missing j=0 intermediate term on p. 275 of Federer
    3.2.38, and the unchanged whole theorem on p. 274.
    An actual unit-length compact line cube and zero map have
    positive tube quotient at every positive radius, although
    the printed j=1 sum is zero. Their actual whole upper
    content and original Jacobian integral are both zero. *)
Example compact_minkowski_constant_map_correction_example (R:realType) (r:R):
  0<r ->exists K g,is_missing_steiner_constant_example r K g /\
    upper_minkowski_content 1 (g @` K)=0%E /\euclidean_jacobian_measure g K=0%E.
Proof.
move=>hr; have [K [g hExample]]:=missing_steiner_constant_counterexample_exists hr.
pose X:=inner_metric_space (@euclidean_inner_productP R 1).
have hBound:=missing_constant_lipschitz hExample.
have hLip:is_metric_lipschitz setT g.
  exists 1; split; first exact:ltr01.
  split; first exact:ler01.
  move=>x y hx hy; have h:=hBound.2 x y hx hy.
  rewrite mul0r mul1r in h *; exact:le_trans h (mdist_ge0 x y).
pose j:=@euclidean_linear_jacobian R 1 1 1 (0:Hom (R_n R 1) (R_n R 1)).
have hOrdinary x:partial_function_graph (@euclidean_jacobian R 1 1 1 setT g) x j.
  apply:(euclidean_jacobian_graph 1 setT g x j).2.
  exists 0; split; first exact:missing_constant_differential hExample x.
  reflexivity.
have hGraph x:partial_function_graph (extended_euclidean_jacobian g) x j%:E.
  exists j; split; [exact:hOrdinary x|reflexivity].
have hJBound:=@euclidean_jacobian_global_upper_bound R 1 1 g 0 (lexx 0) hBound 0 j%:E (hGraph 0).
have hJZero:j=0.
  apply/eqP; rewrite eq_le -!lee_fin.
  apply/andP; split; first by rewrite expr1 in hJBound.
  exact:extended_euclidean_jacobian_nonnegative (hGraph 0).
have hCritical:K `<=` singular_differential_locus g.
  move=>x hx; apply:(singular_differential_locus_jacobian g x).2.
  by rewrite -hJZero; exact:hOrdinary x.
have hNu:=critical_jacobian_measure_zero hCritical.
have hUpper:=compact_lipschitz_image_upper_minkowski (leqnn 1) hLip (missing_constant_compact hExample).
rewrite hNu in hUpper.
exists K,g; split=>//; split; last exact hNu.
apply/eqP; rewrite eq_le hUpper.
exact:(minkowski_contents_nonnegative 1 (g @` K)).2.
Qed.

(** Source for [compact_minkowski_zero_source_positive_atom_example]:
    the source-dimension-zero boundary of Federer 3.2.38,
    p. 274. The actual singleton source and constant image
    retain unit upper content and unit original Jacobian integral.
    This tests the positive atom omitted by the printed m>0
    radius division, rather than applying that division at zero. *)
Example compact_minkowski_zero_source_positive_atom_example (R:realType):
  let X:=inner_metric_space (@euclidean_inner_productP R 0) in
  let Y:=inner_metric_space (@euclidean_inner_productP R 1) in
  let f:X->Y:=fun _=>0 in
  let C:set X:=[set (0:X)] in
  upper_minkowski_content 0 (f @` C)= 1%E /\euclidean_jacobian_measure f C= 1%E /\
    is_measure_subset_integral (@euclidean_lebesgue_measure R 0) C (extended_euclidean_jacobian f) 1%E.
Proof.
move=>X Y f C.
have hLip:is_metric_lipschitz setT f.
  exists 1; split; first exact:ltr01.
  split; first exact:ler01.
  move=>x y _ _; rewrite /f mdistxx mul1r; exact:mdist_ge0.
have hImage:f @` C=[set (0:Y)].
  apply/seteqP; split; first by move=>y [x hx <-].
  move=>y ->; exists (0:X); reflexivity.
have hCount:@counting_measure R Y [set (0:Y)]= 1%E.
  rewrite counting_measure_sum nonnegative_sum_singleton; first reflexivity.
  by rewrite lee_fin ler01.
have hUpper:upper_minkowski_content 0 (f @` C)= 1%E.
  by rewrite hImage (zero_minkowski_contents_counting [set (0:Y)]).1.
have hCm:measure_measurable (@euclidean_lebesgue_measure R 0) C.
  apply:euclidean_borel_measurable; exact:closed_borel_set (compact_closed (@metric_hausdorff R X) (@compact_set1 X 0)).
have hNu:euclidean_jacobian_measure f C= 1%E.
  by rewrite -(zero_source_minkowski_image_jacobian_identity hLip hCm).
split=>//; split=>//; rewrite -hNu; exact:euclidean_jacobian_measure_integral hLip hCm.
Qed.

(** Source for [compact_minkowski_empty_original_source_example]:
    the actual empty compact C in Federer 3.2.38, p. 274,
    in every admissible dimension including zero. The whole theorem
    gives an actual original-domain subset integral of zero and
    zero upper content, without introducing a dummy tube centre. *)
Example compact_minkowski_empty_original_source_example (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)):
  (m<=n)%N ->is_metric_lipschitz setT f ->
  upper_minkowski_content m (f @` set0)=0%E /\
    euclidean_jacobian_measure f set0=0%E /\
    is_measure_subset_integral (@euclidean_lebesgue_measure R m) set0 (extended_euclidean_jacobian f) 0%E.
Proof.
move=>hmn hLip.
have hImage:f @` set0=set0 by apply/seteqP; split=>[y [x []]|y []].
have hNu:euclidean_jacobian_measure f set0=0%E:=measure_empty (euclidean_jacobian_measure_is_measure hLip).
have hUpper:upper_minkowski_content m (f @` set0)=0%E by rewrite hImage; exact:(@minkowski_contents_empty R n m).1.
split=>//; split=>//; rewrite -hNu.
exact:euclidean_jacobian_measure_integral hLip (measure_measurable_empty (euclidean_lebesgue_is_measure R m)).
Qed.

(** Federer (1969), 3.2.39, pp. 275--276: actual
    positive atoms and repeated positive-length image pieces test
    both the whole theorem and its multiplicity-layer argument. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  ClosedRectifiableMinkowski MinkowskiContents PartialFunctionUP RectifiableSetUP
  HausdorffMeasure HausdorffCountingMeasure HausdorffClosedCoverAgreement BorelRegularMeasureUP
  EuclideanLebesgueDimensions EuclideanLebesgueBoxes EuclideanHausdorffLebesgue CoordinateEdgeBoxGeometry EuclideanBoundedRectifiability
  FiniteExceptionalBorel FiniteFamilyLayersUP FiniteFamilyLayerCompactness FiniteFamilyLayerMeasureSum
  MeasureUP MeasureBasic MeasureFiniteAdditivity TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [closed_rectifiable_two_atom_minkowski_example]:
    the genuine finite-set degree-zero convention in Federer
    3.2.39, pp. 275--276, using 3.2.14, p. 252.
    The two actual line points zero and one have common
    Minkowski content two. A single R^0 map cannot replace
    this original multipoint set. *)
Example closed_rectifiable_two_atom_minkowski_example (R:realType):
  exists W:set (inner_metric_space (@euclidean_inner_productP R 1)),
    compact W /\is_m_rectifiable 0 W /\
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 1)) 0 W=(2:R)%:E /\
    partial_function_graph (@minkowski_content R 1 0) W (2:R)%:E.
Proof.
pose X:=inner_metric_space (@euclidean_inner_productP R 1).
pose a:X:=0.
pose b:X:=[ffun _:'I_1=>(1:R)].
pose W:set X:=[set a] `|` [set b].
have hDifferent:a!=b.
  apply/eqP=>hEqual.
  have h:=congr1 (fun v:R_n R 1=>v ord0) (esym hEqual).
  rewrite /a /b !ffunE in h; change ((1:R)=0) in h.
  by move:h=>/eqP; rewrite oner_eq0.
have hCompact:compact W:=compactU (@compact_set1 X a) (@compact_set1 X b).
have hRect:is_m_rectifiable 0 W by rewrite /is_m_rectifiable /W finite_setU; split; exact:finite_set1.
have hMeas:=borel_regular_borel_measurable (@hausdorff_measure_is_measure R X 0)
  (@hausdorff_measure_borel_regular R X 0) (finite_metric_set_borel (finite_set1 a)).
have hDisjoint:forall t,[set a] t ->[set b] t ->False.
  move=>t ha hb; have hEq:a=b:=eq_trans (esym ha) hb.
  by move:hDifferent; rewrite hEq eqxx.
have hMass:@hausdorff_measure R X 0 W=(2:R)%:E.
  rewrite /W (measure_disjoint_union hMeas hDisjoint) !hausdorff_zero_singleton -EFinD; reflexivity.
have hFull:=@federer_3_2_39 R 0 1 W (leq0n 1)
  (compact_closed (@metric_hausdorff R X) hCompact) hRect.
rewrite hMass in hFull.
exists W; split=>//; split=>//; by split.
Qed.

(** Source for [closed_rectifiable_zero_ambient_atom_example]:
    the actual ambient-zero singleton in Federer 3.2.39,
    pp. 275--276. Its common, upper and lower contents
    are all one. This keeps the positive atom at m=n=0. *)
Example closed_rectifiable_zero_ambient_atom_example (R:realType):
  let X:=inner_metric_space (@euclidean_inner_productP R 0) in
  let W:set X:=[set (0:X)] in
  partial_function_graph (@minkowski_content R 0 0) W 1%E /\
    upper_minkowski_content 0 W= 1%E /\lower_minkowski_content 0 W= 1%E.
Proof.
move=>X W.
have hCompact:compact W:=@compact_set1 X 0.
have hRect:is_m_rectifiable 0 W:=finite_set1 _.
have hFull:=@federer_3_2_39 R 0 0 W (leqnn 0)
  (compact_closed (@metric_hausdorff R X) hCompact) hRect.
rewrite hausdorff_zero_singleton in hFull.
split; first exact hFull.
exact:(minkowski_content_graph 0 W 1%E).1 hFull.
Qed.

(** Source for [overlapping_unit_segment_layer_mass_example]:
    the finite image layers in Federer 3.2.39, pp. 275--276.
    Two distinct source indices may have the same actual unit
    segment image. Its whole-theorem common content and Hausdorff
    length are one, but the sum
    of the actual layer lengths is two. The comparison must
    retain image multiplicity rather than treating images as
    disjoint or deleting equal-valued family members. *)
Example overlapping_unit_segment_layer_mass_example (R:realType):
  exists (K:set (inner_metric_space (@euclidean_inner_productP R 1)))
    (S:'I_(#|{: 'I_2}|)->set (inner_metric_space (@euclidean_inner_productP R 1))),
    compact K /\@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 1)) 1 K= 1%E /\
    is_finite_family_layers (fun _:'I_2=>K) S /\
    partial_function_graph (@minkowski_content R 1 1) K 1%E /\
    (\sum_j @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 1)) 1 (S j))%E=(2:R)%:E.
Proof.
pose X:=inner_metric_space (@euclidean_inner_productP R 1).
pose beta:=@hausdorff_measure R X 1.
pose K:set X:=coordinate_edge_box (fun _:'I_1=>(1:R)).
have hCompact:compact K:=@coordinate_edge_box_compact R 1 (fun _:'I_1=>(1:R)).
have hLeb:@euclidean_lebesgue_measure R 1 K= 1%E.
  have h:=@euclidean_closed_box R 1 (fun _:'I_1=>(0:R)) (fun _:'I_1=>(1:R)) (fun _=>ler01).
  by rewrite big_ord1 subr0 in h.
have hMass:beta K= 1%E by rewrite /beta (euclidean_hausdorff_spherical_lebesgue K).1.
have hRect:is_m_rectifiable 1 K.
  apply:euclidean_bounded_identity_rectifiable.
  apply:coordinate_edge_box_bounded=>i; exact:ler01.
have hFull:=@federer_3_2_39 R 1 1 K (leqnn 1)
  (compact_closed (@metric_hausdorff R X) hCompact) hRect.
change (partial_function_graph (@minkowski_content R 1 1) K (beta K)) in hFull.
rewrite hMass in hFull.
have [S hLayers]:=@finite_family_layers_exist X [the finType of 'I_2] (fun _=>K).
have hLayerCompact j:compact (S j):=@finite_family_layers_compact R X [the finType of 'I_2]
  (fun _=>K) S (fun _=>hCompact) hLayers j.
have hMeas (A:set X):compact A ->measure_measurable beta A.
  move=>hA; exact:(borel_regular_borel_measurable (@hausdorff_measure_is_measure R X 1)
    (@hausdorff_measure_borel_regular R X 1) (closed_borel_set (compact_closed (@metric_hausdorff R X) hA))).
have hSum:=@finite_family_layer_measure_sum R X [the finType of 'I_2] beta (fun _=>K) S
  (@hausdorff_measure_is_measure R X 1) hLayers (fun _=>hMeas _ hCompact) (fun j=>hMeas _ (hLayerCompact j)).
have hTwoSum:(\sum_(i:'I_2) beta K)%E=(2:R)%:E.
  by rewrite (eq_bigr _ (fun (_:'I_2) _=>hMass)) sumEFin sumr_const card_ord.
rewrite hTwoSum in hSum.
exists K,S; split=>//; split=>//; split=>//; by split.
Qed.

(** Federer (1969), 3.2.40, printed p. 276, first paragraph:
    whole-example regressions at a strictly subcritical exponent
    and the critical exponent. Kneser's second paragraph is deferred. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground EuclideanInnerProduct InnerMetric
  EuclideanCantorProduct HausdorffMeasure MinkowskiContents PowerCantorPairUP
  CantorSquareMinkowskiCounterexample.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [subcritical_cantor_square_minkowski_example]: regression
    of the full first example in Federer 3.2.40, p. 276, at m=1/4.
    The actual compact same-factor square has zero Hausdorff length,
    zero lower content and infinite upper content simultaneously. *)
Example subcritical_cantor_square_minkowski_example (R:realType):
  exists (n:nat->nat) (A:set (real_line_metric R)) (f:R->R),
    is_power_cantor_pair 1 (1/4:R) n A f /\
    compact (euclidean_cantor_product A A) /\
    upper_minkowski_content 1 (euclidean_cantor_product A A)=+oo /\
    lower_minkowski_content 1 (euclidean_cantor_product A A)=0 /\
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 2)) 1
      (euclidean_cantor_product A A)=0.
Proof.
have hm:(0<(1/4:R))%R by lra.
have hmHalf:((1/4:R)<1/2)%R by lra.
have [n [s [A [f [_ [hPair [_ [hCompact [hUpper [hStrict _]]]]]]]]]] :=
  @federer_3_2_40_cantor_square R 1 (1/4:R) ltr01 hm (ltW hmHalf).
have [hLower hNull]:=hStrict hmHalf.
exists n,A,f; split=>//; split=>//; split=>//; by split.
Qed.

(** Source for [critical_cantor_square_minkowski_example]: regression
    of the critical case of Federer 3.2.40, p. 276, at m=1/2
    and nonunit positive gauge coefficient two. The original carrier
    has positive finite lower content and infinite upper content. *)
Example critical_cantor_square_minkowski_example (R:realType):
  exists (n:nat->nat) (A:set (real_line_metric R)) (f:R->R),
    is_power_cantor_pair 2 (1/2:R) n A f /\
    compact (euclidean_cantor_product A A) /\
    upper_minkowski_content 1 (euclidean_cantor_product A A)=+oo /\
    (0<lower_minkowski_content 1 (euclidean_cantor_product A A) < +oo)%E.
Proof.
have hc:(0<(2:R))%R by lra.
have hm:(0<(1/2:R))%R by lra.
have [n [s [A [f [_ [hPair [_ [hCompact [hUpper [_ hCritical]]]]]]]]]] :=
  @federer_3_2_40_cantor_square R 2 (1/2:R) hc hm (lexx _).
exists n,A,f; split=>//; split=>//; split=>//; exact:hCritical erefl.
Qed.

(** Source for [cantor_square_not_genuinely_rectifiable_example]:
    the first paragraph's final inference in Federer 3.2.40,
    p. 276: compactness and finite (indeed zero) Hausdorff length
    do not supply the strong rectifiability hypothesis. The actual
    preceding Cantor square cannot be genuinely one-rectifiable,
    since the proved closed-rectifiable theorem would force upper
    content zero, contradicting its actual infinite upper content. *)
Example cantor_square_not_genuinely_rectifiable_example (R:realType):
  exists E:set (inner_metric_space (@euclidean_inner_productP R 2)),
    compact E /\
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 2)) 1 E=0 /\
    upper_minkowski_content 1 E=+oo /\~is_m_rectifiable 1 E.
Proof.
have [n [A [f [_ [hCompact [hUpper [_ hNull]]]]]]]:=
  subcritical_cantor_square_minkowski_example R.
pose E:=euclidean_cantor_product A A.
exists E; split=>//; split=>//; split=>// hRect.
have hClosed:=compact_closed (@metric_hausdorff R
  (inner_metric_space (@euclidean_inner_productP R 2))) hCompact.
have hEqual:=(closed_rectifiable_minkowski_equalities (leq_addr 1 1) hClosed hRect).1.
rewrite hUpper hNull in hEqual; discriminate.
Qed.
