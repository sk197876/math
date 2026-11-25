(** Federer (1969), 4.1.26, pp. 383–384:
    restriction to a complementary open component
    keeps the original Lebesgue density. These
    supporting original-domain laws use the already
    proved zero extension and subset integrals;
    they require only local mass integrability. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormBoundedLinearTopology
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading AlternatingForms AlternatingPairing PairingLinear CurrentCoefficientNorms CurrentSpaces
  CurrentDomain CurrentMultivectorDual MultivectorDualSealed CurrentDensityAction CurrentDensityUP
  DistributionIntegralFieldUP DistributionIntegrationRepresentationUP CurrentIntegrationCriterion
  OpenCurrentDensityUP CurrentOpenRestriction CurrentOpenRestrictionLocality
  SmoothCompactSet SmoothTestSpaces SmoothTestEvaluation
  EuclideanLebesgueDimensions EuclideanDistributionMeasureContext EuclideanOpenDomainMeasure
  OpenSubspaceMeasure OpenSubspaceSupportedIntegral IsotropyGroupTopology
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureSubsetIntegral
  MeasurableFunctionUP PartialFunctionBasic PartialFunctionPreimages SummableRealFunctionUP
  RealSubsetIntegralGraph
  TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentLebesgueDensityOpenRestriction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation N:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hN:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT:=(real_norm_metric_space hN).
Local Notation V:=(exterior_power X m).
Local Notation VN:=(@current_vector_mass R h2 n m).
Local Notation Leb:=(@euclidean_lebesgue_measure R n).
Local Notation hLeb:=(euclidean_lebesgue_is_measure R n).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior N x).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior N U x.
Local Notation UT:=(current_domain R n U).
Local Notation mu:=(@euclidean_open_domain_measure R n U).
Local Notation hMu:=(proj1 (@euclidean_open_domain_measure_laws R n U hU)).
Local Notation hRadon:=(proj2 (@euclidean_open_domain_measure_laws R n U hU)).
Variable xi:X->V.
Hypothesis hField:@is_locally_integrable_current_density R h2 n m Leb xi.

(** Source for [current_lebesgue_density_open_field]:
    the original locally summable density remains
    locally summable over any original open
    subdomain, supporting the constancy step of
    4.1.26, p. 384. Compact-subdomain integrals
    retain their exact source sets. *)
Theorem current_lebesgue_density_open_field:
  @is_locally_integrable_open_current_density R h2 n m U mu
    (fun x:UT=>xi (set_val x)).
Proof.
have hXi:=integrable_dual_field_weak_measurable hField.
split.
- constructor.
  + rewrite partial_function_total_domain;exact:measure_almost_everywhere_true hMu.
  + move=>O hO;rewrite partial_function_total_preimage.
    apply:(@open_subspace_preimage_measurable R XT U Leb (xi @^-1` O)).
    have hPre:=measurable_function_open_preimage hXi hO.
    by rewrite partial_function_total_preimage in hPre.
- move=>K hK.
  pose I:set XT:=set_val @` K.
  have hI:compact I.
    exact:(continuous_compact (continuous_subspaceT (@set_type_val_continuous XT U)) hK).
  pose J:=@Build_smooth_compact_set R X N hN Full I (fun _ _=>Logic.I) hI.
  have[b hB]:=integrable_dual_field_local_norm hField J.
  pose g:=fun x:X=>if pselect (I x) then VN (xi x) else 0.
  have hOff:forall x,~U x->g x=0.
    move=>x hx;rewrite /g;case:pselect=>hIx;last reflexivity.
    have[y _ hy]:=hIx;exfalso;apply:hx;rewrite -hy;exact:set_valP y.
  have hOpen:@open XT U.
    rewrite openE=>x hx;exact:(@norm_domain_interior_neighbourhood R X N hN U x).1 (@hU x hx).
  have hUMeas:measure_measurable Leb U:=@euclidean_distribution_measure_borel R n U (open_borel_set hOpen).
  have hPull:=@open_subspace_supported_total_integral R XT U Leb hLeb hUMeas g b%:E hOff hB.
  exists b;apply:(@real_subset_integral_total R UT mu K
    (fun x=>VN (xi (set_val x))) (fun x=>g (set_val x)) b%:E _ _).2 hPull.
  + move=>x hx;rewrite /g;case:pselect=>hIx;first reflexivity.
    exfalso;apply:hIx;exists x;by [].
  + move=>x hx;rewrite /g;case:pselect=>hIx;last reflexivity.
    have[y hy hEq]:=hIx.
    have hYX:y=x:=val_inj hEq.
    by rewrite hYX in hy.
Qed.

(** Source for [current_lebesgue_density_open_action]:
    the actual open restriction has the literal
    original Lebesgue-density representation on U,
    supporting the component argument of 4.1.26,
    p. 384. No mass or representation
    assumption beyond the given density action is added. *)
Theorem current_lebesgue_density_open_action
    (T:@full_current_space R h2 n m):
  @is_current_density_action R h2 n m Leb xi T->
  @is_current_integration_representation R h2 n m U hU
    (@current_open_restriction R h2 n m U Full hU hFull (fun _ _=>Logic.I) T)
    mu (fun x:UT=>xi (set_val x)).
Proof.
move=>hAction.
have hLocal:=current_lebesgue_density_open_field.
constructor;[exact:hMu|exact:hRadon|exact:hLocal.1|exact:hLocal.2|].
move=>psi.
pose P:=@current_open_test_extension R h2 n m U Full hU hFull (fun _ _=>Logic.I).
pose value:=@current_test_value R h2 n U hU m.
pose g:=fun x:X=>pairing (xi x) (value psi x).
have hOriginal:=hAction (P psi).
have hIntegrand:(fun x:X=>pairing (xi x) (current_test_value (P psi) x))=g.
  apply:funext=>x;by rewrite /g /value current_open_test_extension_values.
rewrite hIntegrand in hOriginal.
have hOff:forall x,~U x->g x=0.
  move=>x hx.
  have hZero:value psi x=0:=@smooth_test_value_outside R X (A_m X R^o m)
    N (@current_form_comass R h2 n m) hN (@current_form_comass_real_norm R h2 n m)
    U (@current_smooth_space R h2 n U hU m)
    (@current_smooth_value R h2 n U hU m) (@current_smooth_space_laws R h2 n U hU m)
    psi x hx.
  by rewrite /g hZero -pairing_rightE linear0.
have hOpen:@open XT U.
  rewrite openE=>x hx;exact:(@norm_domain_interior_neighbourhood R X N hN U x).1 (@hU x hx).
have hUMeas:measure_measurable Leb U:=@euclidean_distribution_measure_borel R n U (open_borel_set hOpen).
rewrite current_open_restriction_evaluation.
have hPull:=@open_subspace_supported_total_integral R XT U Leb hLeb hUMeas g
  (@current_value R h2 n Full hFull m T (P psi))%:E hOff hOriginal.
have hPairing:(fun x:UT=>@MultivectorDual.evaluation R X m
    (xi (set_val x)) (value psi (set_val x)))=
    (fun x:UT=>g (set_val x)).
  apply:funext=>x;exact:MultivectorDual.laws.
change (is_measure_integral mu (real_total_integrand
  (fun x:UT=>@MultivectorDual.evaluation R X m (xi (set_val x))
    (value psi (set_val x))))
  (@current_value R h2 n Full hFull m T (P psi))%:E).
by rewrite hPairing.
Qed.
End CurrentLebesgueDensityOpenRestriction.
