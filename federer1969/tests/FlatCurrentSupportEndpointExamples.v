(** Actual-space endpoint regressions for Federer (1969),
    4.1.15, pp. 372–373. The final support-only map law
    acts on a nonzero point with genuinely different maps
    away from its support. Degree zero remains nonzero in
    R^0, and empty source and target opens require no point. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormRegularity NormRegularityOperations
  NormLocalLipschitzScalarProduct
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanOneCoordinate LipschitzUP LipschitzBasic LipschitzConstant
  CurrentSpaces CurrentEvaluation CurrentDirac DiracCurrentBounds
  CurrentDiracSmooth CurrentCompactSmoothValue CurrentSupportGeometry
  CurrentOpenIdentitySmooth SmoothCompactSet NormalCurrentsUP FlatCurrentsUP
  FlatCurrentFinite FlatCurrentUnion CurrentFlatLipschitzPushforwardSealed
  CurrentFlatLipschitzSupportAgreement CurrentFlatIdentityPushforward
  CurrentFlatPointSupport CurrentFlatPushforwardZero.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section FlatCurrentSupportPointEndpoint.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Local Notation X := (R_n R 1%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R 1%N)).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation hImage := (fun (_:X) (_:True)=>Logic.I).
Local Notation Id := (fun x:X=>x).
Local Notation Z := (fun _:X=>(0:X)).
Local Notation hIdClass := (@current_open_identity_smooth R 1%N Full hFull).
Local Notation hIdLocal := (@norm_class_one_locally_metric_lipschitz R
  X X NX NX hNX hNX Full Id
  ((@norm_class_firstP R X X NX NX hNX hNX Full Id).1 (hIdClass 1%N))).
Local Notation hZLocal := (@metric_lipschitz_is_local R
  (real_norm_metric_space hNX) (real_norm_metric_space hNX) Full Z
  (metric_lipschitz_of_bound (least_metric_lipschitz_bound
    (@metric_lipschitz_constant_map R (real_norm_metric_space hNX)
      (real_norm_metric_space hNX) Full (0:X))))).
Local Notation K := (@smooth_compact_singleton R X NX hNX Full (0:X) Logic.I).
Local Notation T := (@dirac_current R h2 1%N Full hFull (0:X)).

Local Lemma flat_support_endpoint_point_flat:
  @is_flat_current R h2 1%N 0%N Full hFull T.
Proof.
exists K;apply:supported_normal_current_is_flat;split.
- exact:(@dirac_current_normal R h2 1%N Full hFull (0:X) Logic.I).
- exact:(@dirac_current_support_subset R h2 1%N Full hFull (0:X) Logic.I).
Qed.

(** Source for [flat_support_nonzero_point_distinct_maps]: the
    final support-only equality of Federer 4.1.15, p. 372,
    on a nonzero actual Dirac current. Identity and the zero
    map agree exactly where needed and differ at one. *)
Example flat_support_nonzero_point_distinct_maps:
  T<>0 /\ Id (@euclidean_one_embed R 1)<>Z (@euclidean_one_embed R 1) /\
  @CurrentFlatLipschitzPushforward.value R h2 1%N 1%N 0%N
    Full Full hFull hFull Z hImage hZLocal T flat_support_endpoint_point_flat=T.
Proof.
have hNonzero:T<>0.
  move=>hZero;have [psi hPsi]:=@dirac_current_unit_test R h2 1%N
    Full hFull (0:X) Logic.I.
  rewrite hZero (linear0 (@current_value R h2 1%N Full hFull 0%N))
    hom_zeroE in hPsi.
  have hBad:(1:R)=0:=esym hPsi.
  by have:=@oner_neq0 R;rewrite hBad eqxx.
split;first exact:hNonzero.
split.
- move=>hEqual.
  have hScalar:=congr1 (@euclidean_one_project R) hEqual.
  have hBad:(1:R)=0.
    by move:hScalar;rewrite /Id /Z euclidean_one_embedK
      /euclidean_one_project ffunE.
  by have:=@oner_neq0 R;rewrite hBad eqxx.
- have hAgreement:forall x,@current_support R h2 1%N Full hFull 0%N T x->Id x=Z x.
    move=>x hx;have hx0:=@dirac_current_support_subset R h2 1%N
      Full hFull (0:X) Logic.I x hx.
    by rewrite /Id /Z hx0.
  have hSame:=@current_flat_lipschitz_support_agreement R h2 1%N 1%N 0%N
    Full Full hFull hFull Id Z hImage hImage hIdLocal hZLocal T
    flat_support_endpoint_point_flat hAgreement.
  have hIdentity:=@current_flat_lipschitz_identity_pushforward R h2 1%N 0%N
    Full hFull hImage hIdLocal T flat_support_endpoint_point_flat.
  exact:(eq_trans (esym hSame) hIdentity).
Qed.
End FlatCurrentSupportPointEndpoint.

Section FlatCurrentSupportZeroDimensionEndpoint.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Local Notation X := (R_n R 0%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 0%N)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R 0%N)).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation K := (@smooth_compact_singleton R X NX hNX Full (0:X) Logic.I).
Local Notation T := (@dirac_current R h2 0%N Full hFull (0:X)).

(** Source for [flat_support_zero_dimensional_point_formula]: the
    degree-zero point formula in Federer 4.1.15, p. 373,
    remains T=1 delta_0 for a nonzero actual R^0 current.
    This checks the printed positive/zero degree distinction. *)
Example flat_support_zero_dimensional_point_formula:
  forall hCompact:@compact (real_norm_metric_space hNX)
      (@current_support R h2 0%N Full hFull 0%N T),
    @current_compact_total R h2 0%N Full hFull T hCompact= 1 /\
    T=@current_compact_total R h2 0%N Full hFull T hCompact*:T.
Proof.
move=>hCompact.
have hFlat:@is_flat_current R h2 0%N 0%N Full hFull T.
  exists K;apply:supported_normal_current_is_flat;split.
  - exact:(@dirac_current_normal R h2 0%N Full hFull (0:X) Logic.I).
  - exact:(@dirac_current_support_subset R h2 0%N Full hFull (0:X) Logic.I).
split.
- exact:(@dirac_current_total R h2 0%N Full hFull (0:X) Logic.I hCompact).
- exact:(@current_flat_zero_point_support R h2 0%N Full hFull
    (0:X) Logic.I T hFlat
    (@dirac_current_support_subset R h2 0%N Full hFull (0:X) Logic.I) hCompact).
Qed.
End FlatCurrentSupportZeroDimensionEndpoint.

Section FlatCurrentSupportEmptyEndpoint.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Local Notation X := (R_n R 0%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 0%N)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R 0%N)).
Local Notation Empty := (fun _:X=>False).
Local Notation hEmpty := (fun (x:X) (hx:False)=>
  False_ind (norm_domain_interior NX Empty x) hx).
Local Notation f := (fun x:X=>x).
Local Notation g := (fun _:X=>(0:X)).
Local Notation hImage := (fun (x:X) (hx:False)=>hx).
Local Notation hClass := (@current_open_identity_smooth R 0%N Empty hEmpty).
Local Notation hLocal := (@norm_class_one_locally_metric_lipschitz R X X NX NX
  hNX hNX Empty f ((@norm_class_firstP R X X NX NX hNX hNX Empty f).1
    (hClass 1%N))).
Local Notation hGLocal := (@metric_lipschitz_is_local R
  (real_norm_metric_space hNX) (real_norm_metric_space hNX) Empty g
  (metric_lipschitz_of_bound (least_metric_lipschitz_bound
    (@metric_lipschitz_constant_map R (real_norm_metric_space hNX)
      (real_norm_metric_space hNX) Empty (0:X))))).
Local Notation hFlat := (@flat_current_zero R h2 0%N 0%N Empty hEmpty).

(** Source for [flat_support_empty_opens_zero]: the actual final
    image of zero in empty source and target opens, a boundary
    case of Federer 4.1.15, p. 372, with no selected target point. *)
Example flat_support_empty_opens_zero:
  @CurrentFlatLipschitzPushforward.value R h2 0%N 0%N 0%N
    Empty Empty hEmpty hEmpty f hImage hLocal 0 hFlat=
    @CurrentFlatLipschitzPushforward.value R h2 0%N 0%N 0%N
      Empty Empty hEmpty hEmpty g hImage hGLocal 0 hFlat /\
  @CurrentFlatLipschitzPushforward.value R h2 0%N 0%N 0%N
    Empty Empty hEmpty hEmpty g hImage hGLocal 0 hFlat=0.
Proof.
split.
- apply:(@current_flat_lipschitz_support_agreement R h2 0%N 0%N 0%N
    Empty Empty hEmpty hEmpty f g hImage hImage hLocal hGLocal 0 hFlat).
  move=>x hx;exact:False_ind _ hx.1.
- exact:(@current_flat_lipschitz_pushforward_zero R h2 0%N 0%N 0%N
    Empty Empty hEmpty hEmpty g hImage hGLocal hFlat).
Qed.
End FlatCurrentSupportEmptyEndpoint.
