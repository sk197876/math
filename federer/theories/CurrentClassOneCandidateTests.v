(** Federer (1969), 4.1.14, p. 372: first prove
    the class-one image identity on every original compact
    target test. Use the genuine class-one approximation,
    the original universal convergence requirement, the preceding
    smooth image test integral and the exact source
    restriction action. The candidate image is arbitrary. *)
From mathcomp Require Import all_boot all_order all_algebra functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormClassOneUP
  NormClassHigherRestriction NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates LipschitzUP
  AlternatingForms AlternatingDual CurrentCoefficientNorms CurrentSpaces CurrentDomain
  CurrentIntegrationCriterion NormalisedCurrentSealed CurrentOriginalBallFormula CurrentMapDifferential
  SmoothCompactSet SmoothCompactNeighbourhoods SmoothTestSpaces SmoothTestEvaluation
  CurrentLipschitzCompactImage FlatCurrentsUP FlatCurrentFinite
  CurrentOpenRestriction CurrentOpenRestrictionVariation CurrentOpenRestrictionContinuousAction
  CurrentFlatOpenRestriction CurrentCompactPushforwardAlgebra
  CurrentCompactLipschitzPushforwardUP CurrentFlatSequenceLimits
  CurrentWeakSequenceLimit NormSequenceLimitUnique
  CurrentCompactSmoothApproximationUP CurrentCompactSmoothApproximationOriginal
  CurrentClassOneSmoothApproximation CurrentClassOnePullbackApproximation
  CurrentSmoothApproximationUP CurrentSmoothTestLoneAction CompactCurrentLoneSequenceLimit
  PartialFunctionBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentClassOneCandidateTests.
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
Hypothesis hT:@is_integration_representable_current R h2 n m U hU T.
Variable Q:@current_space R h2 nu V hV m.
Hypothesis hCandidate:@is_current_compact_lipschitz_image R h2 n nu m
  U V hU hV f hImage hLocal K T Q.
Local Notation UT := (current_domain R n U).
Local Notation mu := (@NormalisedCurrent.measure R h2 n m U hU T hT).
Local Notation xi := (@NormalisedCurrent.auxiliary_density R h2 n m U hU T hT).
Local Notation hRep := (@NormalisedCurrent.laws R h2 n m U hU T hT).
Local Notation I := (@current_representation_lone_integral R h2 n m U hU T mu xi hRep).
Local Notation D := (@current_map_differential R n nu U f).
Local Notation value := (@current_test_value R h2 nu V hV m).
Local Notation fK := (@current_lipschitz_compact_image R n nu U V hU f hImage hLocal K).

(** Source for [current_class_one_candidate_test_action]:
    every candidate satisfying the original compact image
    specification has the class-one pullback action on
    every original compact target test, supporting Federer
    4.1.14, p. 372. The current is flat and
    represented, without normality; finite-mass consumers derive
    the representation by the preceding original theorem. *)
Theorem current_class_one_candidate_test_action
    (psi:@current_test_space R h2 nu V hV m):
  @current_value R h2 nu V hV m Q psi=
  I (partial_function_total (fun x:UT=>
    (A_m_dual (hom_as_linear (D (set_val x)))
      (value psi (f (set_val x))):real_norm_metric_space hPN))).
Proof.
have[Z [g hFamily]]:=@current_class_one_smooth_approximation_exists R n nu
  U V hU hV K f hClass hImage.
have[L hOrdinary]:=current_class_one_smooth_ordinary hFamily.
pose hZ:=current_compact_smooth_domain_open hOrdinary.
pose hKZ:=current_compact_smooth_domain_contains hOrdinary.
pose hZU:=@current_compact_smooth_domain_in_domain R n nu U V K f L Z g hOrdinary.
pose KZ:=@current_compact_index_in_open R n U Z K hKZ.
pose S:=@current_open_restriction R h2 n m Z U hZ hU hZU T.
have hSFlat:=@flat_current_open_restriction R h2 n m U Z hU hZ hZU K hKZ T hFlat.
pose hCompactS:=@flat_supported_current_compact R h2 n m Z hZ KZ S hSFlat.
pose hCompactT:=@flat_supported_current_compact R h2 n m U hU K T hFlat.
have hTZ:@current_support R h2 n U hU m T `<=` Z.
  move=>x hx.
  have hxK:=@flat_current_supported_support R h2 n m U hU K T hFlat x hx.
  exact:(@hKZ x hxK).
pose hSRep:=@current_neighbourhood_restriction_representable R h2 n m
  Z U hZ hU hZU T hT hTZ.
pose muS:=@NormalisedCurrent.measure R h2 n m Z hZ S hSRep.
pose xiS:=@NormalisedCurrent.auxiliary_density R h2 n m Z hZ S hSRep.
pose hRepS:=@NormalisedCurrent.laws R h2 n m Z hZ S hSRep.
pose IS:=@current_representation_lone_integral R h2 n m Z hZ S muS xiS hRepS.
pose ZT:=current_domain R n Z.
have hG:=@current_compact_smooth_original_approximation R n nu U V K f L Z g hOrdinary.
pose P:=fun i=>@current_compact_map_pushforward R h2 n nu Z V hZ hV
  (g i) (current_smooth_approximation_image hG i)
  (current_smooth_approximation_class hG i) m S hCompactS.
have[E hInterior]:=@smooth_compact_neighbourhood_exists R Y NY hNY nu
  (@coordinate_basis R nu) (@coordinate_basisP R nu) V hV fK.
have hInteriorK x (hx:smooth_compact_carrier K x):
    norm_domain_interior NY (smooth_compact_carrier E) (f x).
  apply:hInterior;by exists x.
have hRecovery:=@flat_current_neighbourhood_inclusion_recovery R h2 n m
  U Z hU hZ hZU K hKZ T hFlat hCompactS.
have hLimit:=(proj2 hCandidate) E hInteriorK Z hZ hZU hKZ S hSFlat hRecovery g hG.
have hWeak:=@current_flat_sequence_limit_weak R h2 nu m V hV E P Q hLimit.
have hPsi:norm_class_zero NY QN V (value psi).
  exact:(norm_class_continuous
    (@smooth_test_value_smooth R Y (A_m Y R^o m) NY QN hNY
      (@current_form_comass_real_norm R h2 nu m) V
      (@current_smooth_space R h2 nu V hV m)
      (@current_smooth_value R h2 nu V hV m)
      (@current_smooth_space_laws R h2 nu V hV m) psi 0%N)).
pose w:=fun x=>A_m_dual (hom_as_linear (D x)) (value psi (f x)).
pose wG:=fun i x=>A_m_dual
  (hom_as_linear (@current_map_differential R n nu Z (g i) x)) (value psi (g i x)).
have hW:norm_class_zero NX PN U w.
  exact:(@current_class_one_continuous_pullback R h2 n nu m U V f
    hClass hImage (value psi) hPsi).
have hWZ:norm_class_zero NX PN Z w.
  exact:(@norm_class_zero_open_restriction R X (A_m X R^o m) NX PN U Z w hZU hZ hW).
have hWG i:norm_class_zero NX PN Z (wG i).
  have hFirst:norm_class_one NX NY Z (g i).
    exact:((@norm_class_firstP R X Y NX NY hNX hNY Z (g i)).1
      (current_smooth_approximation_class hG i 1%N)).
  exact:(@current_class_one_continuous_pullback R h2 n nu m Z V (g i)
    hFirst (current_smooth_approximation_image hG i) (value psi) hPsi).
have hUniform:=@current_class_one_pullback_approximation_uniform R h2 n nu m
  U V f hClass hImage (value psi) hPsi K Z g hFamily.
have hSourceLimit:=@compact_current_lone_sequence_limit_on_support R h2 n m
  Z hZ S hSRep hCompactS w wG hWZ hWG.
have hLoneLimit:forall epsilon:R,0<epsilon->exists k,forall i,(k<=i)%N->
    `|IS (partial_function_total (fun x:ZT=>(wG i (set_val x):
        real_norm_metric_space hPN)))-
      IS (partial_function_total (fun x:ZT=>(w (set_val x):
        real_norm_metric_space hPN)))|<epsilon.
  apply:hSourceLimit=>epsilon hEpsilon.
  have[N hN]:=hUniform epsilon hEpsilon.
  exists N=>i hNi x hx.
  have hxK:=@flat_current_supported_support R h2 n m Z hZ KZ S hSFlat x hx.
  exact:(@hN i hNi x hxK).
have hSmoothAction i:IS (partial_function_total
    (fun x:ZT=>(wG i (set_val x):real_norm_metric_space hPN)))=
    @current_value R h2 nu V hV m (P i) psi.
  exact:(@current_smooth_test_lone_pullback_action R h2 n nu m Z V hZ hV
    (g i) (current_smooth_approximation_image hG i)
    (current_smooth_approximation_class hG i) S hSRep hCompactS psi).
have hTestLimit:@current_value R h2 nu V hV m Q psi=
    IS (partial_function_total (fun x:ZT=>(w (set_val x):real_norm_metric_space hPN))).
  apply:(@norm_sequence_limit_unique R R^o (fun a:R^o=>`|a|)
    (@scalar_absolute_value_norm R) (fun i=>@current_value R h2 nu V hV m (P i) psi)).
  - exact:hWeak psi.
  - move=>epsilon hEpsilon;have[N hN]:=hLoneLimit epsilon hEpsilon.
    exists N=>i hNi;rewrite -(hSmoothAction i);exact:(@hN i hNi).
rewrite hTestLimit.
exact:(@current_neighbourhood_continuous_action R h2 n m U Z hU hZ hZU
  T hT hTZ hSRep hCompactT w hW).
Qed.
End CurrentClassOneCandidateTests.
