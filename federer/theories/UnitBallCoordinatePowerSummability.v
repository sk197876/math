(** Federer 2.10.27, p. 191: finite integrability of the
    coordinate-power function used to evaluate the real ball-section
    profile. Reuse the actual Gaussian product integral of 3.2.13,
    p. 250, and domination. No integrability at a zero coordinate
    or at a fractional radial endpoint is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology lra ring num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  InnerNormedTopology MetricClosedBalls EulerGamma EuclideanLebesgueDimensions EuclideanLebesgueBoxes GaussianProductIntegrand GammaGaussianProductIntegral
  SphereCoordinateParameters SphereCoordinateIntegrand RealPower RealExponentialUP
  RealExponentialSealed RealExponentialLaws RealExponentialDifferential ScalarDifferentialContinuity
  RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialZeroExtension
  PartialDensityProduct PartialAbsolutePartsGraph PartialExtendedOrderLoci
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP SummableRealFunctionUP
  MeasurableFunctionUP MeasurableRealEmbedding MeasurableDensityProduct MeasurableGraphEquivalence
  MeasurableZeroExtension RealSubsetIntegralGraph MeasureAbsoluteSummability SummableRealArithmetic
  TopologicalBorel BorelFunctionBasic CompactSupportSummability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Close Scope ereal_scope.

(** Source for [is_unit_ball_coordinate_power]: independent exact
    value laws for the supporting coordinate integrand in the real
    profile evaluation of Federer 2.10.27, p. 191. Use the original
    closed unit ball and the already specified real power at zero. *)
Definition is_unit_ball_coordinate_power (R:realType) n (i:'I_n) (q:R)
    (g:inner_metric_space (@euclidean_inner_productP R n)->R):Prop:=
  (forall x,inner_norm (@euclidean_inner_productP R n) x<=1 ->g x=real_power `|x i| q) /\
  (forall x,1<inner_norm (@euclidean_inner_productP R n) x ->g x=0).

(** Source for [unit_ball_coordinate_power_nonnegative]: sign law
    for the supporting unit-ball integrand of Federer 2.10.27,
    p. 191, from its exact values, including singular real powers. *)
Lemma unit_ball_coordinate_power_nonnegative (R:realType) n (i:'I_n) (q:R) g:
  is_unit_ball_coordinate_power i q g ->forall x,0<=g x.
Proof.
move=> hg x;case:(leP (inner_norm (@euclidean_inner_productP R n) x) 1)=>hx.
- rewrite hg.1 //;exact:real_power_nonnegative.
- by rewrite hg.2.
Qed.

(** Source for [unit_ball_coordinate_power_gaussian_bound]: supporting
    finite Gaussian domination for the profile integral of Federer
    2.10.27, p. 191. The actual Gaussian product supplies the same
    coordinate power; its reciprocal exponential is bounded on the ball. *)
Lemma unit_ball_coordinate_power_gaussian_bound (R:realType) n (i:'I_n) (q:R) g:
  is_unit_ball_coordinate_power i q g ->forall x,
    `|g x|<=RealExponential.exponential (1:R)*
      gaussian_product_integrand (sphere_coordinate_parameters i q) x.
Proof.
move=> hg x.
pose N:=inner_norm (@euclidean_inner_productP R n).
pose E:=@RealExponential.exponential R.
pose G:=gaussian_product_integrand (sphere_coordinate_parameters i q).
have hG:0<=G x.
  rewrite /G /gaussian_product_integrand;apply:mulr_ge0.
  - exact:ltW (real_exponential_positive (@RealExponential.laws R) _).
  - exact:gaussian_angular_nonnegative.
have hValue:E ((N x)^+2)*G x=real_power `|x i| q.
  rewrite /G /gaussian_product_integrand sphere_coordinate_angular_integrand /N /E mulrA
    -(real_exponential_add (@RealExponential.laws R)) addrN
    (real_exponential_zero (@RealExponential.laws R)) mul1r;by [].
rewrite (ger0_norm (unit_ball_coordinate_power_nonnegative hg x)).
case:(leP (N x) 1)=>hx.
- rewrite (hg.1 x hx) -hValue.
  have hExpBound:E ((N x)^+2)<=E 1.
    rewrite /E real_exponential_order.
    have hN:0<=N x:=inner_norm_nonnegative (@euclidean_inner_productP R n) x.
    nra.
  exact (ler_wpM2r hG hExpBound).
- rewrite (hg.2 x hx);apply:mulr_ge0=> //.
  exact:ltW (real_exponential_positive (@RealExponential.laws R) _).
Qed.

(** Source for [unit_ball_coordinate_power_summable]: finite
    integrability needed for the real-degree profile evaluation in
    Federer 2.10.27, p. 191. Reuse the actual Gaussian product
    integral of 3.2.13 and 2.4.9 domination. Measurability and
    summability of the original coordinate integrand are conclusions. *)
Theorem unit_ball_coordinate_power_summable (R:realType) n (i:'I_n) (q:R) g:
  -1<q ->is_unit_ball_coordinate_power i q g ->
  is_measure_summable (@euclidean_lebesgue_measure R n) (real_total_integrand g).
Proof.
move=> hq hg.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose mu:=@euclidean_lebesgue_measure R n.
pose hm:=euclidean_lebesgue_is_measure R n.
pose N:=inner_norm (@euclidean_inner_productP R n).
pose E:=@RealExponential.exponential R.
pose G:=gaussian_product_integrand (sphere_coordinate_parameters i q).
pose F x:=E ((N x)^+2)*G x.
pose B:set X:=[set x|N x<=1].
have hI:=@gamma_gaussian_product_integral R n (sphere_coordinate_parameters i q)
  (sphere_coordinate_parameters_positive i hq).
have hValue x:F x=real_power `|x i| q.
  rewrite /F /G /gaussian_product_integrand sphere_coordinate_angular_integrand /N /E mulrA
    -(real_exponential_add (@RealExponential.laws R)) addrN
    (real_exponential_zero (@RealExponential.laws R)) mul1r;by [].
have hN:continuous (fun x:X=>(N x:R^o)):=norm_continuous.
have hSquare:continuous (fun x:X=>((N x)^+2:real_line_metric R)).
  have he:(fun x:X=>(N x)^+2)=(fun x:X=>N x*N x).
    by apply:funext=>x;rewrite expr2.
  rewrite he=>x;exact:cvgM (hN x) (hN x).
have hExp:continuous (fun x:X=>(E ((N x)^+2):real_line_metric R)).
  move=> x U hU.
  have hCont:=scalar_differential_continuous_at (@real_exponential_differential R ((N x)^+2)).
  exact:(hSquare x _ (hCont U hU)).
have hEMeas:is_measure_measurable_function mu (real_total_integrand (fun x=>E ((N x)^+2))).
  exact:(@continuous_real_integrand_measurable R X mu hm
    (fun A hA=>euclidean_borel_measurable hA) _ hExp).
have hProduct:=measurable_density_product hm hEMeas hI.1.
have hF:is_measure_measurable_function mu (real_total_integrand F).
  apply:(measurable_function_graph_equivalent _ hProduct)=>x z.
  rewrite partial_density_product_graph real_total_integrand_graph;split.
  - move=>[a [b [ha [hb hValue']]]].
    have ha':=(real_total_integrand_graph _ _ _).1 ha.
    have hb':=(real_total_integrand_graph _ _ _).1 hb.
    by rewrite /F -hValue' -ha' -hb' -EFinM.
  - move=> hz;exists (E ((N x)^+2))%:E,(G x)%:E;split.
    + by apply/real_total_integrand_graph.
    + split;first by apply/real_total_integrand_graph.
      by rewrite -EFinM /F hz.
have hB:measure_measurable mu B.
  apply:euclidean_borel_measurable;apply:closed_borel_set.
  have he:B=metric_closed_ball (0:X) 1.
    apply/seteqP;split=>x;by rewrite /B /metric_closed_ball /=
      inner_metric_distanceE sub0r inner_normN.
  rewrite he;exact:metric_closed_ball_closed.
have hZero:=@measurable_zero_extension R X (extended_real_line R) mu hm 0%E B
  (real_total_integrand F) hB hF.
have hOn x (hx:B x):g x=F x by rewrite hValue;exact:(hg.1 x hx).
have hOff x (hx:~B x):g x=0.
  apply:hg.2;rewrite ltNge;apply/negP;exact:hx.
have hMeas:=measurable_function_graph_equivalent (real_subset_total_graph hOn hOff) hZero.
have hGSum:summable_real_functions mu G.
  exists (\prod_j euler_gamma (sphere_coordinate_parameters_positive i hq j)).
  exact hI.
have hDomSummable:summable_real_functions mu (fun x=>E (1:R)*G x).
  exact:(@summable_real_scale R X mu hm G (E (1:R)) hGSum).
apply:(@measure_dominated_summable R X mu hm (real_total_integrand g)
  (real_total_integrand (fun x=>E (1:R)*G x)) hMeas hDomSummable _).1.
apply:(@measure_almost_everywhere_mono R X mu hm setT _ _
  (measure_almost_everywhere_true hm))=>x _.
exists (`|g x|)%:E,(E (1:R)*G x)%:E;split.
- exists (g x)%:E;split;first by apply/real_total_integrand_graph.
  by rewrite abse_EFin.
- split;first by apply/real_total_integrand_graph.
  rewrite lee_fin;exact:(@unit_ball_coordinate_power_gaussian_bound R n i q g hg x).
Qed.
