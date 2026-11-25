(** Federer (1969), 4.1.14, pp. 370–371: the derivative bounds
    on the compact source support bound the masses of smooth images.
    Reuse the sharp proper-pushforward integral from 4.1.7, p. 359,
    its support concentration and the mass bound for exterior powers
    in 1.8.1, p. 39. No normality or finite total mass is required. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm
  HilbertFormCompactness ExteriorGrading CurrentDomain CurrentSpaces
  CurrentCoefficientNorms CurrentMapDifferential EuclideanHomOperator HomSpaceTopology
  OperatorNormUP OperatorNorm CurrentExteriorOperatorMassBound CurrentImageDensityPairing
  CurrentIntegrationCriterion CurrentProperSupport CurrentPushforwardSealed
  CurrentPushforwardMassIntegral CurrentMassSealed CurrentMassRepresentation
  CurrentFiniteMassRepresentation NormalisedCurrentSealed CurrentRadonSupport
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  SmoothCompactSet MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP
  MeasureIntegralComparison MeasureIntegralGraphEquivalence PartialExtendedOrderLoci MeasureStepConstants
  MeasureStepIntegralIdentification PartialFunctionBasic SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentSmoothPushforwardMassBound.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Arguments hV : clear implicits.
Variable T:@current_space R h2 n U hU m.
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.
Hypothesis hSmooth:norm_class_all_orders hNX hNY U f.
Hypothesis hProper:@is_current_proper_on_support R h2 n nu m U hU V T f hImage.
Local Notation Push:=(@CurrentPushforward.value R h2 n nu m U V hU hV
  T f hImage hSmooth hProper).
Local Notation MX:=(@CurrentMass.value R h2 n m U hU).
Local Notation MY:=(@CurrentMass.value R h2 nu m V hV).
Local Notation Support:=(@current_support R h2 n U hU m T).
Local Notation Op:=(@euclidean_operator_norm R n nu).

(** Source for [current_smooth_pushforward_mass_bound_on_support]:
    the estimate M(f#T) <= L^m M(T), used for the original
    approximation sequences in Federer 4.1.14, pp. 370–371. The
    actual derivative bound is required only on spt T. All degrees,
    zero L, empty U and infinite masses retain their original meanings. *)
Theorem current_smooth_pushforward_mass_bound_on_support
    (hT:@is_integration_representable_current R h2 n m U hU T) L:
  0<=L ->(forall x,Support x->Op (@current_map_differential R n nu U f x)<=L) ->
    (MY Push<=(L^+m)%:E*MX T)%E.
Proof.
move=>hL hDerivative.
pose UT:=current_domain R n U.
pose mu:=@NormalisedCurrent.measure R h2 n m U hU T hT.
pose xi:=@NormalisedCurrent.auxiliary_density R h2 n m U hU T hT.
pose hNormal:=@NormalisedCurrent.laws R h2 n m U hU T hT.
pose hm:=distribution_representation_measure (normalised_distribution_representation_laws hNormal).
pose image:=@current_image_density R n nu m U f xi.
pose W:=real_total_integrand (fun x:UT=>@current_vector_mass R h2 nu m (image x)).
have hSupport:measure_almost_everywhere mu [set x:UT|Support (set_val x)].
  exact:(@current_radon_outside_support_null R h2 n m U hU T hT).
have hWeightBound:forall x:UT,Support (set_val x)->
    @current_vector_mass R h2 nu m (image x)<=L^+m.
  move=>x hx.
  pose D:=@current_map_differential R n nu U f (set_val x).
  pose a:=Op D.
  have hA:0<=a by exact:hom_operator_norm_nonnegative.
  have hAL:a<=L:=hDerivative (set_val x) hx.
  have hOperator:is_operator_norm (@euclidean_inner_productP R n)
      (@euclidean_inner_productP R nu) (hom_as_linear D) a.
    exact:(linear_operator_normP (@euclidean_inner_productP R n)
      (@euclidean_inner_productP R nu) (@coordinate_basisP R n) (hom_as_linear D)).
  have hExterior:=@current_exterior_operator_mass_bound R h2 n nu
    (hom_as_linear D) a hOperator m (xi x).
  have hUnit:=normalised_distribution_density_unit_bound hNormal x.
  have hFirst:@current_vector_mass R h2 nu m (image x)<=a^+m.
    have h:=ler_wpM2l (exprn_ge0 m hA) hUnit.
    rewrite mulr1 in h.
    exact:(le_trans hExterior h).
  have hPower:forall j:nat,a^+j<=L^+j.
    elim=>[|j ih];first by rewrite !expr0.
    rewrite !exprS.
    exact:(le_trans (ler_wpM2l hA ih) (ler_wpM2r (exprn_ge0 j hL) hAL)).
  exact:(le_trans hFirst (hPower m)).
have hConstantRaw:=@measure_step_function_integral R UT mu hm _ _
  (@measure_step_constant R UT mu hm (L^+m))
  (@measure_step_constant_integral R UT mu hm (L^+m)).
have hConstant:is_measure_integral mu (real_total_integrand (fun _:UT=>L^+m))
    ((L^+m)%:E*mu setT)%E.
  apply:(@measure_integral_graph_equivalent R UT mu _ _ _ _ hConstantRaw)=>x z;split.
  - move=>[c [<- hz]];by rewrite real_total_integrand_graph.
  - move=>/real_total_integrand_graph hz;exists (L^+m);by split.
have hIntegral:=@current_pushforward_mass_weight_integral R h2 n nu m U V hU hV
  T hT f hImage hSmooth.
have hOrder:measure_almost_everywhere mu
    (partial_extended_le_locus W (real_total_integrand (fun _:UT=>L^+m))).
  apply:(@measure_almost_everywhere_mono R UT mu hm _ _ _ hSupport)=>x hx.
  exists (@current_vector_mass R h2 nu m (image x))%:E,(L^+m)%:E;split.
  - by rewrite real_total_integrand_graph.
  - split;first by rewrite real_total_integrand_graph.
    rewrite lee_fin;exact:hWeightBound x hx.
have hIntegralBound:=@measure_integral_monotone R UT mu hm W
  (real_total_integrand (fun _:UT=>L^+m)) _ _ hIntegral hConstant hOrder.
have hMass:=@current_pushforward_mass_integral_bound R h2 n nu m U V hU hV
  T hT f hImage hSmooth hProper.
rewrite (@current_represented_mass_total R h2 n m U hU T hT).
exact:(le_trans hMass hIntegralBound).
Qed.

(** Source for [current_smooth_pushforward_mass_bound_on_compact]:
    the same estimate from the derivative bound only on the original
    compact K, Federer 4.1.14, pp. 370–371. No bound is required on
    a neighbourhood of K or on the remainder of the open U. *)
Corollary current_smooth_pushforward_mass_bound_on_compact
    (hT:@is_integration_representable_current R h2 n m U hU T)
    (K:smooth_compact_set hNX U) L:
  0<=L ->Support `<=` smooth_compact_carrier K ->
  (forall x,smooth_compact_carrier K x->Op (@current_map_differential R n nu U f x)<=L) ->
    (MY Push<=(L^+m)%:E*MX T)%E.
Proof.
move=>hL hTK hDerivative.
apply:(current_smooth_pushforward_mass_bound_on_support hT hL)=>x hx.
exact:hDerivative x (hTK x hx).
Qed.

(** Source for [current_finite_mass_smooth_pushforward_bound_on_compact]:
    finite-mass pieces of a flat decomposition have the same original
    bound, used in Federer 4.1.14, p. 371. Finite mass supplies
    representability by the preceding 4.1.7 theorem; no normality is assumed. *)
Corollary current_finite_mass_smooth_pushforward_bound_on_compact
    (K:smooth_compact_set hNX U) L:
  (MX T < +oo)%E ->0<=L ->Support `<=` smooth_compact_carrier K ->
  (forall x,smooth_compact_carrier K x->Op (@current_map_differential R n nu U f x)<=L) ->
    (MY Push<=(L^+m)%:E*MX T)%E.
Proof.
move=>hFinite;exact:(current_smooth_pushforward_mass_bound_on_compact
  (@current_finite_mass_representation R h2 n m U hU T hFinite)).
Qed.
End CurrentSmoothPushforwardMassBound.
