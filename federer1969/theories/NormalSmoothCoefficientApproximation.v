(** Federer (1969), 4.1.23, p. 379:
    the smooth-density reduction on the literal
    original open U. The selected coefficient is
    smooth, compactly carried inside Int C,
    has no greater mass, and approximates T
    in the original F_C. No whole-U convexity
    or finite-volume premise is used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormRegularity NormRegularityOperations
  NormBoundedLinearTopology InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading
  CurrentDomain CurrentSpaces CurrentVectorSpaces CurrentCoefficientNorms
  SmoothFunctionSpaceUP SmoothCompactSet SmoothCompactSetExtensionality
  NormalCurrentsUP CurrentMassSealed CurrentFlatNorm
  CurrentOpenRestriction CurrentFlatOpenRestriction CurrentLipschitzCompactImage
  CompactSummableMultivectors CompactSummableMultivectorDensity
  CompactSummableMultivectorAmbient CompactSummableMultivectorOpenRestriction
  EuclideanFullDomainMeasure NormalCurrentAmbientInclusion
  NormalFullSmoothCoefficientApproximation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section OriginalOpenSmoothCoefficient.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation VN := (@current_vector_mass R h2 n m).
Local Notation hVN := (@current_vector_mass_real_norm R h2 n m).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) => norm_full_domain_interior NX x).
Local Notation FT := (current_domain R n Full).
Local Notation WF := (@compact_summable_multivector_space R h2 n m Full hFull).
Local Notation valueF := (@compact_summable_multivector_value R h2 n m Full hFull).
Local Notation rawF := (@compact_summable_multivector_ambient_value R h2 n m Full hFull).
Local Notation imageF := (@compact_summable_multivector_current R h2 n m Full hFull).
Local Notation evF := (@current_vector_smooth_value R h2 n Full hFull m).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Local Notation UT := (current_domain R n U).
Local Notation W := (@compact_summable_multivector_space R h2 n m U hU).
Local Notation value := (@compact_summable_multivector_value R h2 n m U hU).
Local Notation image := (@compact_summable_multivector_current R h2 n m U hU).
Local Notation E := (@current_vector_smooth_space R h2 n U hU m).
Local Notation ev := (@current_vector_smooth_value R h2 n U hU m).
Local Notation M := (@CurrentMass.value R h2 n m U hU).
Local Notation restriction := (@current_open_restriction R h2 n m U Full hU hFull
  (fun _ _ => Logic.I)).

(** Source for [normal_smooth_coefficient_approximation]:
    the second reduction in Federer 4.1.23,
    p. 379, on every original open U.
    The coefficient is a genuine original smooth
    field, identically zero off a compact L
    inside Int C, with the two displayed
    original flat and mass estimates. *)
Theorem normal_smooth_coefficient_approximation
    (K C : smooth_compact_set hNX U)
    (T : @current_space R h2 n U hU m) (delta : R) :
  (forall x, smooth_compact_carrier K x ->
    norm_domain_interior NX (smooth_compact_carrier C) x) ->
  @normal_currents_supported_in R h2 n U hU m K T -> 0<delta ->
  exists f : E, exists xi : W, exists L : smooth_compact_set hNX U,
    value xi=(fun x : UT => ev f (set_val x)) /\
    (forall x, smooth_compact_carrier L x ->
      norm_domain_interior NX (smooth_compact_carrier C) x) /\
    (forall x : UT, ~smooth_compact_carrier L (set_val x) -> value xi x=0) /\
    (@current_flat_norm R h2 n m U hU C (T-image xi)%R<delta%:E)%E /\
    (M (image xi)<=M T)%E.
Proof.
move=> hKC hNormal hDelta.
pose includeU := fun (x : X) (_ : U x) => Logic.I.
pose KF := @current_compact_index_in_open R n U Full K (fun _ _ => Logic.I).
pose CF := @current_compact_index_in_open R n U Full C (fun _ _ => Logic.I).
have [Q [hNQ [hRecovery hMassQ]]] :=
  @normal_current_ambient_inclusion R h2 n m U hU K T hNormal.
have [fF [xiF [LF [hValueF [hLC [hOffF [hError hMass]]]]]]] :=
  @normal_full_smooth_coefficient_approximation R h2 n m KF CF Q delta
    hKC hNQ hDelta.
have hLU : smooth_compact_carrier LF `<=` U.
  move=> x hx.
  have hxC := @norm_domain_interior_member R X NX hNX (smooth_compact_carrier C) x
    (@hLC x hx).
  exact: (@smooth_compact_in_domain R X NX hNX U C x hxC).
pose L := @Build_smooth_compact_set R X NX hNX U (smooth_compact_carrier LF)
  hLU (smooth_compact_is_compact LF).
have hRawOff x : ~smooth_compact_carrier LF x -> rawF xiF x=0.
  move=> hx; pose p := @euclidean_full_domain_point R n x.
  have hInside := @compact_summable_multivector_ambient_inside R h2 n m Full hFull xiF p.
  change (rawF xiF x=valueF xiF p) in hInside.
  rewrite hInside; exact: (@hOffF p hx).
have [xi [hValue [hRaw [hSize [hSupport [hCarrier hCurrent]]]]]] :=
  @compact_summable_multivector_open_restriction R h2 n m U hU xiF
    (smooth_compact_carrier LF) (smooth_compact_is_compact LF) hLU hRawOff.
have hRawSmooth x : rawF xiF x=evF fF x.
  pose p := @euclidean_full_domain_point R n x.
  have hInside := @compact_summable_multivector_ambient_inside R h2 n m Full hFull xiF p.
  change (rawF xiF x=valueF xiF p) in hInside.
  by rewrite hInside hValueF.
have hClass : norm_class_all_orders hNX hVN U (evF fF).
  move=> k; apply: (@norm_class_open_restriction R X (exterior_power X m)
    NX VN hNX hVN Full U (evF fF) k includeU hU).
  exact: (smooth_function_evaluation_smooth
    (@current_vector_smooth_space_laws R h2 n Full hFull m) fF k).
have [f hF] := @smooth_function_evaluation_surjective R X (exterior_power X m)
  NX VN hNX hVN U E ev (@current_vector_smooth_space_laws R h2 n U hU m)
  (evF fF) hClass.
have hXiValue : value xi=(fun x : UT => ev f (set_val x)).
  apply: funext=> x; rewrite hValue hRawSmooth.
  exact: esym (@hF (set_val x) (set_valP x)).
have hBack : @current_compact_index_in_open R n Full U CF
    (smooth_compact_in_domain C)=C.
  by apply: smooth_compact_set_extensionality.
have hNorm := @current_open_restriction_flat_norm_le R h2 n m Full U
  hFull hU includeU CF (smooth_compact_in_domain C) (Q-imageF xiF)%R.
rewrite hBack (linB (hom_linear restriction)) hRecovery -hCurrent in hNorm.
have hErrorU := le_lt_trans hNorm hError.
have hMassU : (M (image xi)<=M T)%E.
  rewrite (@compact_summable_multivector_current_mass R h2 n m U hU xi) hSize
    -(@compact_summable_multivector_current_mass R h2 n m Full hFull xiF).
  exact: le_trans hMass hMassQ.
exists f,xi,L; split; first exact: hXiValue.
split; first exact: hLC.
split; first exact: hCarrier.
split; [exact: hErrorU|exact: hMassU].
Qed.
End OriginalOpenSmoothCoefficient.
