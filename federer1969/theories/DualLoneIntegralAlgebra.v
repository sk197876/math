(** Federer (1969), 4.1.5, p. 350:
    the integral extension is linear and invariant
    under almost equality. The proof uses earlier
    total-representative and scalar integral laws;
    every assertion retains the original conull
    partial-function domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic
  PartialNormedArithmetic MeasurableNormedFunctionUP MeasurableNormedBasic
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralUniqueness
  MeasureIntegralAlmostEquality MeasureIntegralGraphEquivalence MeasureLpMembershipUP MeasureLpAlmostEquality
  MeasureLpScaleMembership MeasureLpSumMembership SummableRealFunctionUP SummableRealArithmetic
  AbstractDualPartialPairing DualLoneIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section DualLoneIntegralAlgebra.
Variable R:realType.
Variable X:choiceType.
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable D:lmodType R.
Variable ed:Hom D (Hom Y R^o).
Variable xi:X->D.
Variable mu:set X->\bar R.
Hypothesis hm:is_measure mu.
Variable I:partial_function X (real_norm_metric_space hNY)->R.
Hypothesis hI:@is_dual_lone_integral R X Y NY hNY D ed xi mu I.

(** Source for [dual_lone_integral_almost_equal]: null
    changes do not change the original L1
    extension, Federer 4.1.5, p. 350,
    using 2.4.9, p. 85. *)
Theorem dual_lone_integral_almost_equal (f g:partial_function X (real_norm_metric_space hNY)):
  is_measure_lp_function mu 1 f ->is_measure_lp_function mu 1 g ->
  measure_almost_equal mu f g ->I f=I g.
Proof.
move=>hf hg hAlmost.
have hPair:measure_almost_equal mu (abstract_dual_partial_pairing ed xi f)
    (abstract_dual_partial_pairing ed xi g).
  apply:(@measure_almost_everywhere_mono R X mu hm _ _ _ hAlmost)=>x [y [hy hGy]].
  exists (ed (xi x) y)%:E; split; apply/abstract_dual_partial_pairing_graph;
    exists y; by split.
have hIntegral:=measure_integral_almost_equal hm (@hI f hf) hPair.
have hEq:=measure_integral_unique hIntegral (@hI g hg).
by injection hEq.
Qed.

(** Source for [dual_lone_integral_total_action]: the exact
    real integral for a total L1 representative,
    Federer 4.1.5, p. 350. *)
Lemma dual_lone_integral_total_action (f:X->real_norm_metric_space hNY):
  is_measure_lp_function mu 1 (partial_function_total f) ->
  is_measure_integral mu (real_total_integrand (fun x=>ed (xi x) (f x)))
    (I (partial_function_total f))%:E.
Proof.
move=>hf.
exact:(measure_integral_graph_equivalent
  (@abstract_dual_partial_pairing_total_graph R X Y D ed xi f)
  (@hI (partial_function_total f) hf)).
Qed.

(** Source for [dual_lone_integral_total_linear]: addition
    and all real scalings, including zero, for
    total representatives of the original L1
    extension, Federer 4.1.5, p. 350. *)
Theorem dual_lone_integral_total_linear (c:R) (f g:X->real_norm_metric_space hNY):
  is_measure_lp_function mu 1 (partial_function_total f) ->
  is_measure_lp_function mu 1 (partial_function_total g) ->
  is_measure_lp_function mu 1 (partial_function_total
    (fun x=>(c*:f x+g x:real_norm_metric_space hNY))) ->
  I (partial_function_total (fun x=>(c*:f x+g x:real_norm_metric_space hNY)))=
    c*I (partial_function_total f)+I (partial_function_total g).
Proof.
move=>hf hg hSum.
have hScaled:=@real_total_integral_scale R X mu hm (fun x=>ed (xi x) (f x))
  (I (partial_function_total f)) c (dual_lone_integral_total_action hf).
have hCombined:=@real_total_integral_add R X mu hm (fun x=>c*ed (xi x) (f x))
  (fun x=>ed (xi x) (g x)) (c*I (partial_function_total f))
  (I (partial_function_total g)) hScaled (dual_lone_integral_total_action hg).
have hActual:=dual_lone_integral_total_action hSum.
have hValues:(fun x=>ed (xi x) (c*:f x+g x))=
    (fun x=>c*ed (xi x) (f x)+ed (xi x) (g x)).
  apply:funext=>x; exact:(hom_linear (ed (xi x)) c (f x) (g x)).
rewrite hValues in hActual.
have hEq:=measure_integral_unique hActual hCombined.
by injection hEq.
Qed.

(** Source for [dual_lone_integral_linear]: full original
    L1 linearity with the exact common conull
    domain for c f+g, Federer 4.1.5,
    p. 350. No total-domain premise is added. *)
Theorem dual_lone_integral_linear (c:R) (f g:partial_function X (real_norm_metric_space hNY)):
  is_measure_lp_function mu 1 f ->is_measure_lp_function mu 1 g ->
  I (partial_vector_add (partial_vector_scale c f) g)=c*I f+I g.
Proof.
move=>hf hg.
have[F [_ [hFAlmost hFMeasurable]]]:=@measurable_normed_total_representative R X Y NY hNY mu hm f hf.2.1.
have[G [_ [hGAlmost hGMeasurable]]]:=@measurable_normed_total_representative R X Y NY hNY mu hm g hg.2.1.
have hF:=@measure_lp_function_almost_equal R X Y NY hNY mu hm 1 f (partial_function_total F) hf hFAlmost.
have hG:=@measure_lp_function_almost_equal R X Y NY hNY mu hm 1 g (partial_function_total G) hg hGAlmost.
have hScaled:=@measure_lp_function_scale R X Y NY hNY mu hm 1 c f hf.
have hSum:=@measure_lp_function_add R X Y NY hNY mu hm 1 _ g hScaled hg.
pose H:=fun x=>(c*:F x+G x:real_norm_metric_space hNY).
have hAlmost:measure_almost_equal mu (partial_vector_add (partial_vector_scale c f) g) (partial_function_total H).
  apply:(@measure_almost_everywhere_mono R X mu hm _ _ _
    (@measure_almost_everywhere_and R X mu hm _ _ hFAlmost hGAlmost)).
  move=>x [[u [hu hFu]] [v [hv hGv]]].
  exists (c*:u+v); split.
  - apply/partial_vector_add_graph; exists (c*:u),v; split.
    + apply/partial_vector_scale_graph; exists u; by split.
    + by split.
  - change (H x=c*:u+v).
    by rewrite /H (hFu:F x=u) (hGv:G x=v).
have hH:=@measure_lp_function_almost_equal R X Y NY hNY mu hm 1 _ (partial_function_total H) hSum hAlmost.
have hValues:=@dual_lone_integral_total_linear c F G hF hG hH.
rewrite /H in hValues.
rewrite (dual_lone_integral_almost_equal hSum hH hAlmost)
  (dual_lone_integral_almost_equal hf hF hFAlmost)
  (dual_lone_integral_almost_equal hg hG hGAlmost).
exact hValues.
Qed.
End DualLoneIntegralAlgebra.
