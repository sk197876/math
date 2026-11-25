(** Federer (1969), 4.1.25, p. 383: apply 4.1.2,
    p. 347, to obtain bounded almost-everywhere convergence
    of the differentials of smoothings. This supporting statement
    treats one arbitrary direction and retains every actual
    differential value. The finite coordinate family will give
    convergence of the whole differential. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP
  VectorDaniellHypotheses NormDifferentialUP NormDifferentialDirectional
  NormedCurveDerivativeUP NormClassZeroWhole NormRegularity LipschitzUP
  NormMetricScaleContinuity MetricLocalLipschitzContinuity
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness Rademacher EuclideanOwnNormCompleteness
  EuclideanOwnNormSeparable EuclideanLebesgueDimensions
  NormDirectionalBoundedRepresentative LocallyIntegrableVectorFieldUP
  LocallyBoundedMeasurableFieldIntegrability SmoothingKernelUP
  SmoothingDilationUP SmoothingDilationSmooth SmoothingDilationNonzeroRadius
  SmoothingConvolutionUP SmoothingConvolutionExistence
  SmoothingLocalLipschitzInput ContinuousSmoothingSmoothness
  SmoothingLebesguePoint MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureLebesgueSet PartialFunctionBasic CurrentMapDifferential
  CurrentLipschitzLebesgueActionLebesguePoints
  CurrentLipschitzLebesgueActionCoordinateLimit EuclideanHomOperator
  FiniteCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section LebesgueActionSmoothingAE.
Variable R : realType.
Variables m n : nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation YT := (real_norm_metric_space hNY).
Local Notation mu := (@euclidean_lebesgue_measure R m).
Local Notation hm := (euclidean_lebesgue_is_measure R m).
Variable f : X -> Y.
Variable L : R.
Hypothesis hL : 0 <= L.
Hypothesis hLip : forall x y, NY (f x-f y) <= L*NX (x-y).
Variable phi : X -> R.
Hypothesis hPhi : is_smoothing_kernel phi.
Variable family : R -> X -> R.
Hypothesis hFamily : is_smoothing_dilation phi family.
Variable g : R -> X -> Y.
Hypothesis hConvolution : forall e, 0 < e ->
  is_smoothing_convolution hNY (family e) f (g e).

(** Source for [current_lipschitz_lebesgue_action_smoothing_direction_ae]:
    the bounded almost-everywhere differential limit used in
    4.1.25, p. 383, obtained in each direction from
    4.1.2, p. 347, and 2.9.9, pp. 156–157.
    Rank-deficient and zero differentials remain in the actual
    graph. No evenness of the smoothing kernel is assumed. *)
Theorem current_lipschitz_lebesgue_action_smoothing_direction_ae (v:X) :
  measure_almost_everywhere mu [set a |
    forall D:Hom X Y, has_norm_differential NX NY setT f a D ->
    forall eta:R, 0 < eta -> exists delta:R, 0 < delta /\
      forall e:R, 0 < e -> e < delta ->
        NY (@current_map_differential R m n setT (g e) a v-D v) < eta].
Proof.
have hPositive : 0 < L+1 := ltr_wpDl hL ltr01.
have hWide x y : NY (f x-f y) <= (L+1)*NX (x-y).
  apply:le_trans (hLip x y) _.
  apply:ler_wpM2r; first exact:real_seminorm_nonnegative hNX.1 (x-y).
  by rewrite lerDl.
have hMetric : @is_metric_lipschitz R XT YT setT f.
  exists (L+1); split=>//; split; [exact: ltW hPositive | move=>x y _ _].
  exact:hWide x y.
have hInnerMetric : @is_metric_lipschitz R
    (inner_metric_space (@euclidean_inner_productP R m))
    (inner_metric_space (@euclidean_inner_productP R n)) setT f.
  exists (L+1); split=>//; split; [exact: ltW hPositive | move=>x y _ _].
  exact:hWide x y.
have hLocal : @is_locally_metric_lipschitz R XT YT setT f.
  move=>x _; exists setT; split; first exact:filterT.
  exists (L+1); split=>//; split; [exact: ltW hPositive | move=>x' y' _ _].
  exact:hWide x' y'.
have hContinuous := metric_local_lipschitz_continuous_whole hLocal.
have hDifferentiable := @federer_3_1_6 R m n f hInnerMetric.
have hDirectional : measure_almost_everywhere mu [set a |
    exists w:Y, punctured_norm_limit NY
      (fun t=>t^-1*:(f (a+t*:v)-f a)) w].
  apply:(@measure_almost_everywhere_mono R X mu hm _ _ _ hDifferentiable).
  move=>a [D hD]; exists (D v).
  exact:(@norm_differential_directional_limit R X Y NX NY hNX hNY
    setT f a D hD v).
have [xi [hRep [hZero [hBound [hMeas hXiAE]]]]] :=
  @norm_directional_bounded_representative_exists R m Y NY hNY
    f L hL hLip v hContinuous hDirectional.
have hField : @is_locally_integrable_vector_field R X Y NX NY hNX hNY mu xi.
  apply:(@locally_bounded_measurable_field_locally_integrable
    R m Y NY hNY xi hMeas)=>K.
  exists (L*NX v); split.
  - exact:mulr_ge0 hL (real_seminorm_nonnegative hNX.1 v).
  - by move=>x _; exact:hBound x.
have hSep := @euclidean_own_norm_separable R n.
have [C [hCc hCd]] := hSep.
have hLebesgue := @current_lipschitz_lebesgue_action_bounded_lebesgue_points
  R m Y NY hNY C xi (L*NX v) hCc hCd hMeas hBound.
have hExists e : exists q:X->Y,
    0 < e -> is_smoothing_convolution hNY (family e) xi q.
  case:(pselect (0<e))=>he.
  - have [q hq] := @smoothing_convolution_exists R m Y NY hNY
      (@euclidean_own_norm_complete R n) hSep
      phi hPhi family hFamily e he xi hField.
    by exists q.
  - exists (fun _=>0); by move=>he'; contradiction.
have [q hQ] := choice hExists.
have hSmooth e (he:0<e) : norm_class_all_orders hNX hNY setT (g e).
  exact:(@continuous_smooth_convolution_smooth R m Y NY hNY
    (@euclidean_own_norm_complete R n) f
    (norm_continuous_whole_class_zero hContinuous) (family e) e (g e)
    (@smoothing_dilation_smooth R m phi hPhi family hFamily e he)
    (@smoothing_dilation_zero_beyond_radius R m phi family hPhi hFamily e he)
    (@hConvolution e he)).
have hValue e (he:0<e) a :
    @current_map_differential R m n setT (g e) a v = q e a.
  have hActual := @current_map_differential_actual R m n setT (g e)
    (@hSmooth e he) a Logic.I.
  have hD := @norm_differential_directional_limit R X Y NX NY hNX hNY
    setT (g e) a _ hActual v.
  have hQDerivative := @smoothing_local_lipschitz_input_derivative R m Y NY hNY
    (@euclidean_own_norm_complete R n) hSep phi hPhi family hFamily e he
    f xi (g e) (q e) hLocal v hRep hZero hXiAE
    (@hConvolution e he) (@hQ e he) a.
  apply: (@punctured_norm_limit_unique R _ NY _ _ _ _ hD hQDerivative).
  exact: hNY.
apply:(@measure_almost_everywhere_mono R X mu hm _ _ _ hLebesgue)=>a hA D hD eta hEta.
have hDirectionalValue := @norm_differential_directional_limit R X Y NX NY hNX hNY
  setT f a D hD v.
have hXiValue : xi a=D v := @hRep a (D v) hDirectionalValue.
have [delta [hDelta hLimit]] := @smoothing_at_centered_lebesgue_point R m
  Y NY hNY hSep phi hPhi family hFamily xi hField q hQ a hA eta hEta.
exists delta; split=>//e he hSmall.
rewrite (@hValue e he a) -hXiValue.
exact:@hLimit e he hSmall.
Qed.

(** Source for [current_lipschitz_lebesgue_action_smoothing_differential_ae]:
    the whole differential converges almost everywhere in its
    original operator norm, as used in the first proof
    of 4.1.25, p. 383. This is a finite
    intersection of the preceding directional limits, not an
    additional hypothesis on an operator-valued derivative field. *)
Theorem current_lipschitz_lebesgue_action_smoothing_differential_ae :
  measure_almost_everywhere mu [set a |
    forall D:Hom X Y, has_norm_differential NX NY setT f a D ->
    forall eta:R, 0<eta -> exists delta:R, 0<delta /\
      forall e:R, 0<e -> e<delta ->
        @euclidean_operator_norm R m n
          (@current_map_differential R m n setT (g e) a-D)<eta].
Proof.
have hEach (i:'I_m) := current_lipschitz_lebesgue_action_smoothing_direction_ae
  (@coordinate_basis R m i).
have hAll := @measure_almost_everywhere_countable R X 'I_m
  mu hm setT _ (@countableP _ setT) (fun i _=>hEach i).
apply:(@measure_almost_everywhere_mono R X mu hm _ _ _ hAll)=>a hA D hD.
apply:current_lipschitz_lebesgue_action_coordinate_limit=>i.
exact:(@hA i Logic.I D hD).
Qed.
End LebesgueActionSmoothingAE.
