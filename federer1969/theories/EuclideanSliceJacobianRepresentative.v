(** Federer (1969), 3.2.10, p. 248: measurable
    nonnegative representatives of the last-block Jacobian of Dv.
    Specify agreement with every actual differential before proving
    existence, using only existing opaque extension interfaces. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerMetric NormMetric EuclideanHomOperator HomSpaceNormTopology
  NormDifferentialUP NormFiniteLinearBound NormBoundedLinearTopology
  EuclideanBlockLinearMaps EuclideanLinearJacobian EuclideanJacobianContinuity
  EuclideanDifferentialObservables EuclideanLebesgueDimensions MeasureUP
  PartialFunctionUP PartialFunctionBasic PartialFunctionExtensionUP MeasurableFunctionUP MeasurableTotalExtension
  MeasurableFiniteRealParts LipschitzUP RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_hom_precompose_continuous]: the
    restriction of Dv to complementary directions in Federer
    3.2.10, p. 248, depends continuously on Dv. This
    supporting linear-topology fact uses finite dimension only. *)
Lemma euclidean_hom_precompose_continuous (R:realType) m n k
    (j:Hom (R_n R k) (R_n R m)):
  continuous (fun L:real_norm_metric_space (@euclidean_operator_norm_is_norm R m n)=>
    (hom_comp L j:real_norm_metric_space (@euclidean_operator_norm_is_norm R k n))).
Proof.
pose NX:=@euclidean_operator_norm R m n.
pose NY:=@euclidean_operator_norm R k n.
pose hNX:=@euclidean_operator_norm_is_norm R m n.
pose hNY:=@euclidean_operator_norm_is_norm R k n.
have [q [b hb]]:=@hom_space_finite_basis R (R_n R m) (R_n R n)
  m (@coordinate_basis R m) (@coordinate_basisP R m)
  n (@coordinate_basis R n) (@coordinate_basisP R n).
pose A:=@HomMap R (Hom (R_n R m) (R_n R n)) (Hom (R_n R k) (R_n R n))
  (fun L=>hom_comp L j) (introT (asboolP _) (hom_precompose_linear j)).
have hBound:norm_bounded_linear NX NY A:=norm_finite_linear_bounded hNX hNY hb A.
exact (@norm_bounded_linear_continuous R (Hom (R_n R m) (R_n R n))
  (Hom (R_n R k) (R_n R n)) NX NY hNX hNY A hBound).
Qed.

(** Source for [euclidean_precomposed_top_jacobian_continuous]:
    the complementary Jacobian in Federer 3.2.10, p. 248,
    is continuous in its ambient differential. The fixed
    source map may be any linear map, including an empty frame. *)
Lemma euclidean_precomposed_top_jacobian_continuous (R:realType) m n k
    (j:Hom (R_n R k) (R_n R m)):
  continuous (fun L:real_norm_metric_space (@euclidean_operator_norm_is_norm R m n)=>
    (euclidean_linear_jacobian k (hom_comp L j):real_line_metric R)).
Proof.
move=>L; exact (continuous_comp (@euclidean_hom_precompose_continuous R m n k j L)
  (@euclidean_top_jacobian_continuous R k n (hom_comp L j))).
Qed.

(** Source for [is_euclidean_slice_jacobian_representative]:
    supporting scalar weight in the Fubini calculation of
    Federer 3.2.10, p. 248. It is nonnegative and
    measurable, and agrees with the complementary Jacobian at
    every actual differentiability point of v. This predicate
    assumes no chosen differential or new mathematical axiom. *)
Definition is_euclidean_slice_jacobian_representative (R:realType) m n k
    (v:R_n R (n+k)->R_n R m) (g:R_n R (n+k)->real_line_metric R):Prop:=
  (forall w,0<=g w) /\
  is_measure_measurable_function (@euclidean_lebesgue_measure R (n+k)) (partial_function_total g) /\
  forall w M,has_norm_differential (inner_norm (@euclidean_inner_productP R (n+k)))
    (inner_norm (@euclidean_inner_productP R m)) setT v w M ->
    g w=euclidean_linear_jacobian k (hom_comp M (@euclidean_last_injection_map R n k)).

(** Source for [euclidean_slice_jacobian_representative_exists]:
    existence of the measurable complementary Jacobian weight
    in Federer 3.2.10, p. 248. A local total extension
    is made nonnegative by its positive part; exact agreement
    on the actual differential domain is preserved. No new
    globally chosen object or exposed construction is introduced. *)
Theorem euclidean_slice_jacobian_representative_exists (R:realType) m n k
    (v:inner_metric_space (@euclidean_inner_productP R (n+k))->
      inner_metric_space (@euclidean_inner_productP R m)):
  is_metric_lipschitz setT v ->exists g,is_euclidean_slice_jacobian_representative v g.
Proof.
move=>hv; pose h:=fun M:Hom (R_n R (n+k)) (R_n R m)=>
  euclidean_linear_jacobian k (hom_comp M (@euclidean_last_injection_map R n k)).
have hMeas:=@euclidean_differential_observable_measurable R (n+k) m v h hv
  (@euclidean_precomposed_top_jacobian_continuous R (n+k) m k
    (@euclidean_last_injection_map R n k)).
have [F [hExt [_ hF]]]:=measurable_function_total_extension
  (euclidean_lebesgue_is_measure R (n+k)) (0:real_line_metric R) hMeas.
exists (fun w=>Num.max (F w) 0); split.
- move=>w; by rewrite le_max lexx orbT.
- split; first exact (measurable_finite_real_parts (euclidean_lebesgue_is_measure R (n+k)) hF).1.
  move=>w M hM.
  have hGraph:partial_function_graph (euclidean_differential_observable v h) w (h M).
    apply:(euclidean_differential_observable_graph v h w _).2; exists M; by split.
  have hEq:=hExt w (h M) hGraph.
  rewrite hEq; apply:max_idPl; exact:euclidean_linear_jacobian_nonnegative.
Qed.
