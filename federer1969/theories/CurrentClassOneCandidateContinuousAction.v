(** Federer (1969), 4.1.14, p. 372, final sentence:
    for class-one f and a finite-mass flat T,
    (f#T)(phi)=T(f#phi) for every continuous m-form phi.
    Prove the formula first on actual target tests,
    then use compact uniform approximation and the original
    L1 action bounds on the exact supports K and f(K).
    The candidate satisfies the original independent image law. *)
From mathcomp Require Import all_boot all_order all_algebra functions
  classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormClassOneUP NormRegularity NormCompactFunctionBound InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanHomOperator LipschitzUP
  AlternatingForms AlternatingDual CurrentCoefficientNorms CurrentSpaces CurrentDomain
  CurrentMapDifferential CurrentMapDifferentialNormContinuity
  CurrentIntegrationCriterion NormalisedCurrentSealed CurrentOriginalBallFormula
  CurrentLoneExtension CurrentLoneSequenceLimit CurrentRadonSupport
  CurrentMassSealed CurrentMassBasic CurrentMassRepresentation CurrentFiniteMassRepresentation
  CurrentLipschitzCompactImage FlatCurrentsUP FlatCurrentFinite SmoothCompactSet
  CurrentCompactLipschitzPushforwardUP CurrentNormalLipschitzMassBound
  CurrentClassOneCandidateTests CurrentClassOnePullbackApproximation
  CurrentContinuousTestApproximation CurrentContinuousTestActionBound
  CurrentFormPullbackDifferenceBound CompactCurrentContinuousLoneMember
  SmoothTestSpaces SmoothTestEvaluation NormSequenceLimitUnique
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  PartialFunctionBasic MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureLpMembershipUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentClassOneCandidateContinuousAction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation PN := (@current_form_comass R h2 n m).
Local Notation QN := (@current_form_comass R h2 nu m).
Local Notation hPN := (@current_form_comass_real_norm R h2 n m).
Local Notation hQN := (@current_form_comass_real_norm R h2 nu m).
Local Notation Op := (@euclidean_operator_norm R n nu).
Local Notation hOp := (@euclidean_operator_norm_is_norm R n nu).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Hypothesis hLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U f.
Hypothesis hClass:norm_class_one NX NY U f.
Variable K:smooth_compact_set hNX U.
Variable T:@current_space R h2 n U hU m.
Hypothesis hFlat:@is_flat_current_supported_in R h2 n m U hU K T.
Hypothesis hFinite:(@CurrentMass.value R h2 n m U hU T< +oo)%E.
Variable Q:@current_space R h2 nu V hV m.
Hypothesis hCandidate:@is_current_compact_lipschitz_image R h2 n nu m
  U V hU hV f hImage hLocal K T Q.
Local Notation UT := (current_domain R n U).
Local Notation VT := (current_domain R nu V).
Local Notation D := (@current_map_differential R n nu U f).
Local Notation fK := (@current_lipschitz_compact_image R n nu U V hU f hImage hLocal K).
Local Notation totalT w := (partial_function_total
  (fun x:UT=>(w (set_val x):real_norm_metric_space hPN))).
Local Notation totalQ w := (partial_function_total
  (fun y:VT=>(w (set_val y):real_norm_metric_space hQN))).
Local Notation muT hT := (@NormalisedCurrent.measure R h2 n m U hU T hT).
Local Notation xiT hT := (@NormalisedCurrent.auxiliary_density R h2 n m U hU T hT).
Local Notation repT hT := (@NormalisedCurrent.laws R h2 n m U hU T hT).
Local Notation muQ hQ := (@NormalisedCurrent.measure R h2 nu m V hV Q hQ).
Local Notation xiQ hQ := (@NormalisedCurrent.auxiliary_density R h2 nu m V hV Q hQ).
Local Notation repQ hQ := (@NormalisedCurrent.laws R h2 nu m V hV Q hQ).
Local Notation IT hT := (@current_representation_lone_integral R h2 n m U hU T
  (muT hT) (xiT hT) (repT hT)).
Local Notation IQ hQ := (@current_representation_lone_integral R h2 nu m V hV Q
  (muQ hQ) (xiQ hQ) (repQ hQ)).
Local Notation pull phi := (fun x=>A_m_dual (hom_as_linear (D x)) (phi (f x))).

(** Source for [current_class_one_candidate_continuous_action]:
    the last identity of Federer 4.1.14, p. 372,
    with the original finite-mass flat input, class-one
    map and every continuous target form. Image finite
    mass and both L1 memberships are proved. The final
    equality holds for every original representation witness;
    none is an extra input premise on T or Q. *)
Theorem current_class_one_candidate_continuous_action:
  (@CurrentMass.value R h2 nu m V hV Q< +oo)%E /\
  forall (hT:@is_integration_representable_current R h2 n m U hU T)
    (hQ:@is_integration_representable_current R h2 nu m V hV Q)
    (phi:Y->A_m Y R^o m),
    norm_class_zero NY QN V phi->
    is_measure_lp_function (muQ hQ) 1 (totalQ phi) /\
    is_measure_lp_function (muT hT) 1 (totalT (pull phi)) /\
    IQ hQ (totalQ phi)=IT hT (totalT (pull phi)).
Proof.
have hFiniteQ:=@current_flat_lipschitz_image_finite_mass R h2 n nu m
  U V hU hV f hImage hLocal K T Q hFlat hFinite hCandidate.
split;first exact:hFiniteQ.
move=>hT hQ phi hPhi.
have hSupportT:=@flat_current_supported_support R h2 n m U hU K T hFlat.
have hSupportQ:=@flat_current_supported_support R h2 nu m V hV fK Q hCandidate.1.
pose hCompactT:=@flat_supported_current_compact R h2 n m U hU K T hFlat.
pose hCompactQ:=@flat_supported_current_compact R h2 nu m V hV fK Q hCandidate.1.
have hPull:=@current_class_one_continuous_pullback R h2 n nu m U V f
  hClass hImage phi hPhi.
have hMemberQ:=@compact_represented_current_continuous_lone_member R h2 nu m
  V hV Q hQ hCompactQ phi hPhi.
have hMemberT:=@compact_represented_current_continuous_lone_member R h2 n m
  U hU T hT hCompactT (pull phi) hPull.
split;first exact:hMemberQ.
split;first exact:hMemberT.
have[a [ha hMassT]]:=@current_finite_mass_value R h2 n m U hU T hFinite.
have[b [hb hMassQ]]:=@current_finite_mass_value R h2 nu m V hV Q hFiniteQ.
have hFirst:norm_class hNX hNY U f 1%N.
  exact:((@norm_class_firstP R X Y NX NY hNX hNY U f).2 hClass).
have hD:=@current_class_one_differential_continuous R n nu U f hFirst.
have[C [hCPositive hCBound]]:=@norm_class_zero_compact_bounded R X (Hom X Y)
  NX Op hNX hOp U (smooth_compact_carrier K) D (smooth_compact_is_compact K)
  (smooth_compact_in_domain K) hD.
pose c:=C+1.
have hC:0<=c by rewrite /c;lra.
have hPower:0<=c^+m:=exprn_ge0 m hC.
have hCap x (hx:smooth_compact_carrier K x):Op (D x)<=c.
  have hBound:=hCBound x hx;rewrite /c;lra.
pose A:=b+a*c^+m.
have hA:0<=A:=addr_ge0 hb (mulr_ge0 ha hPower).
have hTotal:(muT hT) setT=a%:E.
  by rewrite -(@current_represented_mass_total R h2 n m U hU T hT) hMassT.
have hmT:=distribution_representation_measure
  (normalised_distribution_representation_laws (repT hT)).
have hAlmostSupport:measure_almost_everywhere (muT hT)
    [set x:UT|@current_support R h2 n U hU m T (set_val x)].
  exact:(@current_radon_outside_support_null R h2 n m U hU T hT).
apply:(@norm_sequence_limit_unique R R^o (fun z:R^o=>`|z|)
  (@scalar_absolute_value_norm R)
  (fun _:nat=>IQ hQ (totalQ phi))
  (IQ hQ (totalQ phi)) (IT hT (totalT (pull phi)))).
- move=>epsilon hEpsilon;exists 0%N=>i _;by rewrite subrr normr0.
- move=>epsilon hEpsilon.
  have hDen:0<A+1 by lra.
  pose error:=epsilon/(A+1).
  have hError:0<error by rewrite /error divr_gt0.
  have[psi hApprox]:=@current_continuous_test_approximation_at_scale R h2 nu m
    V hV fK phi hPhi error hError.
  pose p:=@current_test_value R h2 nu V hV m psi.
  have hPointQ y (hy:smooth_compact_carrier fK y):QN (phi y-p y)<=error.
    rewrite (real_seminorm_subtract hQN.1);exact:ltW (hApprox y hy).
  have hQCap:(@CurrentMass.value R h2 nu m V hV Q<=b%:E)%E.
    by rewrite hMassQ.
  have hTargetBound:=@current_continuous_test_action_error_bound R h2 nu m
    V hV fK Q hQ b error phi psi hQCap hSupportQ hPhi (ltW hError) hPointQ.
  have hP:norm_class_zero NY QN V p.
    exact:(norm_class_continuous
      (@smooth_test_value_smooth R Y (A_m Y R^o m) NY QN hNY hQN V
        (@current_smooth_space R h2 nu V hV m)
        (@current_smooth_value R h2 nu V hV m)
        (@current_smooth_space_laws R h2 nu V hV m) psi 0%N)).
  have hPullP:=@current_class_one_continuous_pullback R h2 n nu m U V f
    hClass hImage p hP.
  have hMemberP:=@compact_represented_current_continuous_lone_member R h2 n m
    U hU T hT hCompactT (pull p) hPullP.
  have hPointSource x (hx:smooth_compact_carrier K x):
      PN (pull phi x-pull p x)<=error*c^+m.
    change (is_true (PN (A_m_dual (hom_as_linear (D x)) (phi (f x))-
      A_m_dual (hom_as_linear (D x)) (p (f x)))<=error*c^+m)).
    rewrite -linearB.
    have hBound:=@current_form_linear_pullback_bound R h2 n nu m (D x) c
      (phi (f x)-p (f x)) hC (hCap x hx).
    apply:le_trans hBound _.
    apply:ler_wpM2r;first exact:hPower.
    apply:hPointQ;by exists x.
  have hPointAlmost:measure_almost_everywhere (muT hT)
      [set x:UT|PN (pull phi (set_val x)-pull p (set_val x))<=error*c^+m].
    apply:(@measure_almost_everywhere_mono R UT (muT hT) hmT _ _ _ hAlmostSupport)
      =>x hx.
    exact:hPointSource (set_val x) (hSupportT (set_val x) hx).
  have hSourceBound:=@current_lone_almost_uniform_action_bound R h2 n m U hU
    T (muT hT) (xiT hT) (repT hT) a (error*c^+m)
    (fun x:UT=>pull phi (set_val x)) (fun x:UT=>pull p (set_val x))
    hTotal hMemberT hMemberP hPointAlmost.
  have hTest:=@current_class_one_candidate_test_action R h2 n nu m
    U V hU hV f hImage hLocal hClass K T hFlat hT Q hCandidate psi.
  rewrite hTest in hTargetBound.
  have hSourceSwap:`|IT hT (totalT (pull p))-IT hT (totalT (pull phi))|
      <=(error*c^+m)*a.
    rewrite (real_seminorm_subtract (@scalar_absolute_value_norm R).1).
    exact:hSourceBound.
  have hTriangle:=real_seminorm_triangle (@scalar_absolute_value_norm R).1
    (IQ hQ (totalQ phi)-IT hT (totalT (pull p)))
    (IT hT (totalT (pull p))-IT hT (totalT (pull phi))).
  have hSplit:(IQ hQ (totalQ phi)-IT hT (totalT (pull p)))+
      (IT hT (totalT (pull p))-IT hT (totalT (pull phi)))=
      IQ hQ (totalQ phi)-IT hT (totalT (pull phi)) by ring.
  rewrite hSplit in hTriangle.
  have hBound:=le_trans hTriangle (lerD hTargetBound hSourceSwap).
  have hAlgebra:error*b+(error*c^+m)*a=error*A by rewrite /A;ring.
  rewrite hAlgebra in hBound.
  have hStrict:error*A<error*(A+1) by rewrite ltr_pM2l // ltrDl.
  rewrite /error divfK ?gt_eqF // in hStrict.
  exists 0%N=>i _;exact:le_lt_trans hBound hStrict.
Qed.
End CurrentClassOneCandidateContinuousAction.
