(** Federer (1969), 4.1.7, p. 358: integration
    representation is local in the original
    current support sense. The proof reuses
    the finite smooth partition of 4.1.1,
    p. 345, and the exact compact gauge
    criterion of 4.1.5, p. 349. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity NormRegularityOperations
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct AlternatingForms
  CurrentCoefficientNorms CurrentSpaces CurrentSupportGeometry CurrentCompactGaugeSupport CurrentIntegrationCriterion
  SmoothCompactSet SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation SmoothMultiplierUP
  SmoothCompactPartitionUP FiniteNormSmoothPartitionExistence SmoothPartitionCompactSelection
  SmoothTestScalarMultiplier SmoothTestFiniteDecomposition CompactSupportFunctionUP FunctionLatticeUP
  DistributionVariationUP DistributionVariationDomain DistributionVariationFinite DistributionVariationBoundedExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentPointwiseRepresentation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation Y := (A_m X R^o m).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation E := (@current_smooth_space R h2 n U hU m).
Local Notation ev := (@current_smooth_value R h2 n U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation C := (@current_space R h2 n U hU m).
Local Notation UT := [the topologicalType of set_type (U:set XT)].
Local Notation values := (smooth_test_values_hom hE).
Local Notation dvalues := (@distribution_domain_values R XT U Y DT values).
Local Notation action := (@current_value R h2 n U hU m).
Local Notation represented := (@is_integration_representable_current R h2 n m U hU).
Local Notation support := (@current_test_support R h2 n m U hU).

(** Source for [current_pointwise_representation]: if
    every point has an open neighbourhood
    on which T agrees with a represented
    current, then T is representable,
    supporting the second local-normality equivalence
    in Federer 4.1.7, p. 358.
    A compact majorant admits one finite
    partition, so no convergence of currents
    or extra countability hypothesis is assumed. *)
Theorem current_pointwise_representation (T:C):
  (forall x,U x->exists W:set X,@open XT W /\ W x /\ W `<=` U /\
    exists S:C,represented S /\forall psi:DT,support psi `<=` W->action T psi=action S psi) ->
  represented T.
Proof.
move=>hLocal.
pose Phi:set (set XT):=[set W|@open XT W /\ W `<=` U /\exists S:C,
  represented S /\forall psi:DT,support psi `<=` W->action T psi=action S psi].
have hOpen W:Phi W->@open XT W by move=>[hW _];exact:hW.
have hDomain:(\bigcup_(W in Phi) W)=U.
  apply:funext=>x;apply:propext;split.
  - move=>[W [hW [hWU hS]] hx];exact:hWU x hx.
  - move=>hx;have[W [hW [hxW [hWU hS]]]]:=hLocal x hx.
    exists W=>//;split=>//;split=>//.
have[J [I [v [hCount [hv hRef]]]]]:=@finite_norm_smooth_partition_exists R X NX hNX n
  (@coordinate_basis R n) (@coordinate_basisP R n) Phi hOpen.
rewrite hDomain in hv.
apply:(@current_integration_finite_gauge_criterion R h2 n m U hU T).1=>f hf.
have[K hK]:=@current_compact_gauge_support R h2 n m U hU f hf.1.
have[F [hFI hInactive]]:=smooth_partition_compact_active_selection hv K.
have hModels (s:F):exists S:C,represented S /\forall psi:DT,
    support psi `<=` @real_function_support R XT (v (val s))->action T psi=action S psi.
  have[W [[hW [hWU [S [hS hAgree]]]] hSW]]:=hRef (val s) (@hFI (val s) (valP s)).
  exists S;split=>// psi hPsi;apply:hAgree=>x hx;exact:hSW x (hPsi x hx).
have[S hS]:=choice hModels.
have hBounds (s:F):exists b:R,0<=b /\forall psi:DT,
    (forall x:UT,NY (dvalues psi x)<=f x)->`|action (S s) psi|<=b.
  have[b hB]:=((@current_integration_finite_gauge_criterion R h2 n m U hU (S s)).2 (hS s).1) f hf.
  exact:(@distribution_variation_finite_iff_bound R UT Y NY hNY DT dvalues
    (action (S s)) f b%:E hf.2 hB).1 (ltry _).
have[b hb]:=choice hBounds.
pose hScalar (s:F) k:=@norm_class_open_restriction R X R^o NX (fun t:R^o=>`|t|) hNX
  (@scalar_absolute_value_norm R) (fun _=>True) U (v (val s)) k (fun _ _=>Logic.I) hU
  (@smooth_partition_global_class R X NX hNX U J I v hv (val s) (@hFI (val s) (valP s)) k).
pose P (s:F):Hom DT DT:=@smooth_test_scalar_multiplier R X Y NX NY hNX hNY U E ev hE
  (v (val s)) (hScalar s).
have hP s:is_smooth_multiplier U (@current_test_value R h2 n U hU m) (v (val s)) (P s).
  exact:smooth_test_scalar_multiplier_laws.
apply:(@distribution_variation_bounded_value_exists R UT Y NY hNY DT dvalues
  (action T) f (\sum_(s:F) b s) hf.2)=>psi hPsi.
have hSum:=@smooth_test_finite_partition_identity R X Y NX NY hNX hNY U E ev hE J I v hv
  K F hFI hInactive P hP psi (hK psi hPsi).
have hAction:action T psi=\sum_(s:F) action (S s) (P s psi).
  have hApplied:=congr1 (action T) hSum.
  rewrite linear_sum in hApplied.
  apply:(eq_trans (esym hApplied));apply:eq_bigr=>s _.
  apply:(hS s).2=>x hx.
  exact:(@smooth_test_scalar_multiplier_support R X Y NX NY hNX hNY U E ev hE
    (v (val s)) (hScalar s) psi x hx).
have hPart (s:F) (x:UT):NY (dvalues (P s psi) x)<=f x.
  change (NY (@current_test_value R h2 n U hU m (P s psi) (set_val x))<=f x).
  rewrite (@hP s psi (set_val x) (set_valP x)) (real_seminorm_scale hNY.1).
  have hRange:=@smooth_partition_global_range R X NX hNX U J I v hv (val s)
    (@hFI (val s) (valP s)) (set_val x).
  have[h0 h1]:=andP hRange.
  rewrite (ger0_norm h0).
  apply:le_trans _ (hPsi x).
  have h:=ler_wpM2r (real_seminorm_nonnegative hNY.1
    (@current_test_value R h2 n U hU m psi (set_val x))) h1.
  by rewrite mul1r in h.
have hAbs:`|action T psi|<=\sum_(s:F) b s.
  rewrite hAction.
  apply:le_trans (@real_seminorm_sum R R^o (fun t=>`|t|)
    (@scalar_absolute_value_norm R).1 F (fun s=>action (S s) (P s psi))) _.
  apply:ler_sum=>s _;exact:(hb s).2 (P s psi) (hPart s).
exact:le_trans (ler_norm _) hAbs.
Qed.
End CurrentPointwiseRepresentation.
