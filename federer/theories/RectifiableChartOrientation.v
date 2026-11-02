(** Federer (1969), 3.2.25, p. 261: a Borel orientation
    on each compact chart image, obtained from the actual
    differential and the same-bound inverse. Auxiliary values
    outside the chart image are never asserted to be unit vectors. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct EuclideanLinearMaps
  InnerNorm InnerMetric HilbertFormCompactness InnerExteriorPositivity ExteriorGrading ExteriorNorm AssociatedSubspace
  NormDifferentialUP NormDifferentialDirectional LinearEmbeddingContinuity NormMetricScaleContinuity
  LipschitzUP LipschitzBasic EuclideanLipschitzClassZero RectifiableCompactChartsUP
  RectifiableChartInverseExtension EuclideanDifferentialVectorObservable EuclideanDifferentialOrientation
  EuclideanDifferentialOrientationContinuity PartialFunctionUP PartialFunctionExtensionUP
  BorelPartialTotalExtension BorelFunctionUP BorelFunctionBasic TopologicalBorel InnerOwnNormTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [uniform_compact_chart_orientation_exists]: the
    local formula for S and T on psi_i(K_i) in 3.2.25,
    p. 261. The exact Borel differential graph gives a
    Borel parameter expression. A same-bound global inverse
    transports it to the image. Chart differential bounds prove
    injectivity and therefore simple unit values at every chart
    point; no derivative field or measurability premise is added. *)
Theorem uniform_compact_chart_orientation_exists (R:realType) m n (lambda:R)
    (K:set (R_n R m)) (psi:R_n R m->R_n R n):
  0<lambda ->is_uniform_compact_rectifiable_chart lambda K psi ->
  let E:=inner_metric_space (@exterior_inner_productP R (euclidean_two_nonzero R)
    (R_n R n) (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m) in
  exists h:inner_metric_space (@euclidean_inner_productP R n)->E,
    is_borel_function h /\forall a,K a ->
      exists D:Hom (R_n R m) (R_n R n),
        has_norm_differential (inner_norm (@euclidean_inner_productP R m))
          (inner_norm (@euclidean_inner_productP R n)) setT psi a D /\
        injective D /\h (psi a)=euclidean_differential_orientation D /\
        simple (h (psi a)) /\
        @exterior_norm R (euclidean_two_nonzero R) (R_n R n)
          (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m (h (psi a))= 1.
Proof.
move=>hLambda hChart E.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose o:=fun D:Hom (R_n R m) (R_n R n)=>(euclidean_differential_orientation D:E).
pose d:=@euclidean_differential_postcompose R m n E psi o.
have hLip:=metric_lipschitz_of_bound (rectifiable_chart_global_bound hChart).
have hBorel (U:set E):open U ->@borel_set X (partial_function_preimage d U).
  move=>hU.
  have hRaw:=@euclidean_differential_postcompose_borel R m n E psi o
    (euclidean_lipschitz_norm_class_zero hLip) (@euclidean_differential_orientation_borel R m n)
    U (open_borel_set hU).
  exact:(inner_own_norm_borel_iff (@euclidean_inner_productP R m) _).2 hRaw.
have [J [hJ [hDefault hJBorel]]]:=@borel_partial_total_extension_exists X E d (0:E) hBorel.
have [G [hG hInverse]]:=uniform_compact_chart_inverse_global_extension hChart.
have hGContinuous:continuous (G:Y->X).
  apply:(metric_fixed_lipschitz_continuous (ltW hLambda))=>w z.
  exact:(hG.2 w z Logic.I Logic.I).
pose h:=fun w:Y=>(J (G w):E).
exists h; split.
- exact:(borel_function_composition (continuous_borel_function hGContinuous) hJBorel).
- move=>a ha.
  have [D [hD hBounds]]:=@rectifiable_chart_differential_bounds R m n lambda K psi hChart a ha.
  have hInjective:injective D.
    apply:(norm_linear_lower_bound_injective
      (inner_norm_real_norm (@euclidean_inner_productP R m))
      (inner_norm_real_norm (@euclidean_inner_productP R n))).
    exists lambda^-1; split; first by rewrite invr_gt0.
    move=>v; exact:(hBounds v).1.
  have hValue:h (psi a)=euclidean_differential_orientation D.
    rewrite /h (hInverse a ha); apply:hJ.
    apply:(@euclidean_differential_postcompose_graph R m n E psi o a (o D)).2.
    exists D; by split.
  have [hSimple hUnit]:=euclidean_differential_orientation_unit_simple hInjective.
  exists D; split; first exact hD; split; first exact hInjective; split; first exact hValue.
  by rewrite hValue; split.
Qed.
