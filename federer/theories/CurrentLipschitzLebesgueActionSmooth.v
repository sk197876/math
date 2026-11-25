(** Federer (1969), 4.1.25, p. 383: the first
    pushforward action is immediate when f is smooth.
    This proof applies the original smooth pullback action
    to the actual compact L1 density current. The
    Lebesgue field is neither normalized nor replaced by
    the current's variation orientation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct ExteriorGrading
  ExteriorMaps AlternatingForms AlternatingDual AlternatingPairing
  CurrentDomain CurrentSpaces CurrentEvaluation CurrentCoefficientNorms
  CurrentMapDifferential CurrentCompactMapProper CurrentCompactPushforwardAlgebra
  CurrentCompactPushforwardTests CurrentCompactSmoothValue CurrentCompactSmoothAgreement
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothTestSpaces
  SmoothCutoffReplacement SmoothFormPullbackUP SmoothFormPullbackSealed
  CompactSummableMultivectors CompactSummableMultivectorDensity
  CompactSummableMultivectorAmbient CompactSummableMultivectorSupport
  CompactSummableFullCurrentAction CurrentLipschitzLebesgueActionDensity
  EuclideanLebesgueDimensions MeasureIntegralUP SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section LebesgueActionSmooth.
Variable R : realType.
Hypothesis h2 : (1+1:R) != 0.
Variables m n k : nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation FullX := (fun _ : X => True).
Local Notation FullY := (fun _ : Y => True).
Local Notation hFullX := (fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation hFullY := (fun (y:Y) (_:True)=>norm_full_domain_interior NY y).
Local Notation FT := (current_domain R m FullX).
Local Notation E := (@current_smooth_space R h2 m FullX hFullX k).
Local Notation ev := (@current_smooth_value R h2 m FullX hFullX k).
Local Notation hE := (@current_smooth_space_laws R h2 m FullX hFullX k).
Local Notation TargetE := (@current_smooth_space R h2 n FullY hFullY k).
Local Notation targetEv := (@current_smooth_value R h2 n FullY hFullY k).
Local Notation hTargetE := (@current_smooth_space_laws R h2 n FullY hFullY k).
Local Notation PN := (@current_form_comass R h2 m k).
Local Notation hPN := (@current_form_comass_real_norm R h2 m k).
Local Notation sourceTest := (@current_test_value R h2 m FullX hFullX k).
Local Notation targetTest := (@current_test_value R h2 n FullY hFullY k).
Variable xi : @compact_summable_multivector_space R h2 m k FullX hFullX.
Local Notation raw := (@compact_summable_multivector_ambient_value
  R h2 m k FullX hFullX xi).
Local Notation T := (@compact_summable_multivector_current R h2 m k FullX hFullX xi).
Local Notation hCompact := (@current_lipschitz_lebesgue_action_density_compact
  R h2 m k FullX hFullX xi).
Variable f : X -> Y.
Hypothesis hf : norm_class_all_orders hNX hNY FullX f.
Local Notation hImage := (fun (x:X) (_:True)=>Logic.I).
Local Notation image := (@current_compact_map_pushforward R h2 m n
  FullX FullY hFullX hFullY f hImage hf k T hCompact).

(** Source for [current_lipschitz_lebesgue_action_smooth]: the
    smooth case of the first displayed formula in
    4.1.25, p. 383, from 4.1.7, p. 359.
    Every compact summable exterior field is allowed; the
    final original top-source degree is a specialization.
    The zero exterior image at a rank-deficient derivative
    is retained in this same integral. *)
Theorem current_lipschitz_lebesgue_action_smooth
    (phi:@current_test_space R h2 n FullY hFullY k) :
  is_measure_integral (@euclidean_lebesgue_measure R m)
    (real_total_integrand (fun x:X =>
      pairing
        (exterior_power_map
          (hom_as_linear (@current_map_differential R m n FullX f x)) k (raw x))
        (targetTest phi (f x))))
    (@current_value R h2 n FullY hFullY k image phi)%:E.
Proof.
have [C [hC [_ hOff]]] := @compact_summable_multivector_ambient_carrier
  R h2 m k FullX hFullX xi.
pose K := @Build_smooth_compact_set R X NX hNX FullX C
  (fun _ _=>Logic.I) hC.
have hFieldOff (x:FT) : ~smooth_compact_carrier K (set_val x) ->
    @compact_summable_multivector_value R h2 m k FullX hFullX xi x=0.
  move=>hx.
  rewrite -(@compact_summable_multivector_ambient_inside R h2 m k FullX hFullX xi x).
  exact:hOff (set_val x) hx.
have hSupport := @compact_summable_multivector_current_support
  R h2 m k FullX hFullX xi K hFieldOff.
pose pb := @SmoothFormPullback.operator R h2 m n k
  FullX FullY hFullX hFullY f hImage hf
  (smooth_test_inclusion hTargetE phi).
pose replace := @smooth_cutoff_replacement R X (A_m X R^o k)
  NX PN hNX hPN m (@coordinate_basis R m) (@coordinate_basisP R m)
  FullX hFullX E ev hE K.
pose psi := replace pb.
have [W [hW [hKW [_ hAgreement]]]] :=
  @smooth_cutoff_replacement_agrees_near_compact R X (A_m X R^o k)
    NX PN hNX hPN m (@coordinate_basis R m) (@coordinate_basisP R m)
    FullX hFullX E ev hE K.
have hValue : @current_value R h2 n FullY hFullY k image phi =
    @current_value R h2 m FullX hFullX k T psi.
  rewrite /image /current_compact_map_pushforward
    (@current_compact_pushforward_test_value R h2 m n k FullX FullY
      hFullX hFullY f hImage hf T _ hCompact phi).
  apply:(@current_compact_near_support_smooth_value R h2 m k
    FullX hFullX T hCompact pb psi W hW (subset_trans hSupport hKW)).
  move=>x hx; symmetry; exact:(hAgreement pb x hx).
have hOriginal := @compact_summable_full_current_action R h2 m k xi psi.
have hPoint : (fun x:X=>pairing (raw x) (sourceTest psi x)) =
    (fun x:X=>pairing
      (exterior_power_map
        (hom_as_linear (@current_map_differential R m n FullX f x)) k (raw x))
      (targetTest phi (f x))).
  apply:funext=>x.
  case:(pselect (smooth_compact_carrier K x))=>hx.
  - have hTest : sourceTest psi x=ev pb x := hAgreement pb x (hKW x hx).
    rewrite hTest.
    have hPullback := @smooth_form_pullback_values R m n k FullX FullY
      TargetE E targetEv ev f
      (@SmoothFormPullback.operator R h2 m n k FullX FullY hFullX hFullY f hImage hf)
      (@SmoothFormPullback.laws R h2 m n k FullX FullY hFullX hFullY f hImage hf)
      (smooth_test_inclusion hTargetE phi) x
      (@current_map_differential R m n FullX f x) Logic.I
      (@current_map_differential_actual R m n FullX f hf x Logic.I).
    rewrite /pb hPullback A_m_dual_pairing.
    reflexivity.
  - have hZero : raw x=0 := hOff x hx.
    rewrite hZero linear0.
    rewrite (Bilinear.lin0 ((@pairing_bilinear R X R^o k).1 (sourceTest psi x)))
      (Bilinear.lin0 ((@pairing_bilinear R Y R^o k).1 (targetTest phi (f x)))).
    reflexivity.
rewrite hPoint -hValue in hOriginal.
exact:hOriginal.
Qed.
End LebesgueActionSmooth.
