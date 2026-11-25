(** Federer (1969), 4.1.14, pp. 370–371: changing
    a map's irrelevant representative outside its original open
    domain does not change the image. Prove agreement
    from the independent compact-image condition, then use
    the original scalar cutoff for local images. Equality
    is assumed on all of U; the later support-only
    coincidence assertion of 4.1.15 is not used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP SmoothCompactSet SmoothCompactSetExtensionality CurrentSpaces CurrentEvaluation
  CurrentLipschitzCompactImage CurrentCompactLipschitzPushforwardUP
  CurrentCompactLipschitzImageUniqueness CurrentSmoothApproximationUP
  CurrentCompactPushforwardAlgebra CurrentPushforwardDataIndependence
  CurrentFlatSequenceLimitUP FlatCurrentsUP CurrentFlatLipschitzPushforwardUP
  CurrentFlatLipschitzPushforwardSealed CurrentProperSupport
  CurrentCommonPushforwardCutoff CurrentContraction SmoothTestSpaces
  CurrentLipschitzPushforwardUP CurrentLipschitzPushforwardSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentLipschitzMapDomainAgreement.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variables f g:X->Y.
Hypothesis hFImage:forall x,U x->V (f x).
Hypothesis hGImage:forall x,U x->V (g x).
Hypothesis hFLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U f.
Hypothesis hGLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U g.
Hypothesis hEqual:forall x,U x->f x=g x.
Arguments hEqual : clear implicits.

(** Source for [current_compact_lipschitz_image_domain_agreement]:
    the original compact-image condition depends only on
    the given map on U, supporting the formal
    properties of Federer 4.1.14, pp. 370–371.
    Transfer exactly the same compact E, source Z,
    representative S and smooth family. No equality
    only on support is assumed. *)
Theorem current_compact_lipschitz_image_domain_agreement
    (K:smooth_compact_set hNX U)
    (T:@current_space R h2 n U hU m)
    (Q:@current_space R h2 nu V hV m):
  @is_current_compact_lipschitz_image R h2 n nu m U V hU hV
    f hFImage hFLocal K T Q ->
  @is_current_compact_lipschitz_image R h2 n nu m U V hU hV
    g hGImage hGLocal K T Q.
Proof.
move=>hQ.
pose fK:=@current_lipschitz_compact_image R n nu U V hU f hFImage hFLocal K.
pose gK:=@current_lipschitz_compact_image R n nu U V hU g hGImage hGLocal K.
have hIndex:fK=gK.
  apply:smooth_compact_set_extensionality.
  apply:funext=>y;apply:propext;split.
  - move=>[x hx <-];exists x;first exact:hx.
    exact:esym (hEqual x (smooth_compact_in_domain K x hx)).
  - move=>[x hx <-];exists x;first exact:hx.
    exact:hEqual x (smooth_compact_in_domain K x hx).
split.
- change (@is_flat_current_supported_in R h2 nu m V hV gK Q).
  rewrite -hIndex;exact:hQ.1.
- move=>E hInside Z hZ hZU hKZ S hS hInclusion q hQG.
  pose KZ:=@current_compact_index_in_open R n U Z K hKZ.
  have hInsideF:forall x,smooth_compact_carrier K x->
      norm_domain_interior NY (smooth_compact_carrier E) (f x).
    move=>x hx;rewrite (hEqual x (smooth_compact_in_domain K x hx)).
    exact:hInside x hx.
  have hQF:@is_current_smooth_approximation R n nu Z V KZ f q.
    constructor.
    + exact:current_smooth_approximation_image hQG.
    + exact:current_smooth_approximation_class hQG.
    + exact:current_smooth_approximation_bound hQG.
    + move=>epsilon hEpsilon.
      have[N hN]:=current_smooth_approximation_uniform hQG hEpsilon.
      exists N=>i hNi x hx.
      rewrite (hEqual x (smooth_compact_in_domain K x hx)).
      exact:hN i hNi x hx.
  pose hCompactS:=@flat_supported_current_compact R h2 n m Z hZ KZ S hS.
  have hLimit:=hQ.2 E hInsideF Z hZ hZU hKZ S hS hInclusion q hQF.
  have hSame:
      (fun i=>@current_compact_map_pushforward R h2 n nu Z V hZ hV
        (q i) (current_smooth_approximation_image hQF i)
        (current_smooth_approximation_class hQF i) m S hCompactS)=
      (fun i=>@current_compact_map_pushforward R h2 n nu Z V hZ hV
        (q i) (current_smooth_approximation_image hQG i)
        (current_smooth_approximation_class hQG i) m S hCompactS).
    apply:funext=>i.
    exact:(@current_pushforward_data_independent R h2 n nu m Z V hZ hV S (q i)
      (current_smooth_approximation_image hQF i) (current_smooth_approximation_image hQG i)
      (current_smooth_approximation_class hQF i) (current_smooth_approximation_class hQG i)
      _ _).
  by rewrite hSame in hLimit.
Qed.

(** Source for [current_flat_lipschitz_pushforward_domain_agreement]:
    maps equal on the original open U have
    equal actual global flat images, among the
    formal properties in Federer 4.1.14, p. 371.
    One original compact index is selected only
    in this proof; every map and carrier stays opaque. *)
Theorem current_flat_lipschitz_pushforward_domain_agreement
    (T:@current_space R h2 n U hU m)
    (hFlat:@is_flat_current R h2 n m U hU T):
  @CurrentFlatLipschitzPushforward.value R h2 n nu m U V hU hV
    f hFImage hFLocal T hFlat=
  @CurrentFlatLipschitzPushforward.value R h2 n nu m U V hU hV
    g hGImage hGLocal T hFlat.
Proof.
have[K hK]:=hFlat.
apply:(@current_compact_lipschitz_image_unique R h2 n nu m U V hU hV
  g hGImage hGLocal K T hK).
- apply:current_compact_lipschitz_image_domain_agreement.
  exact:((@CurrentFlatLipschitzPushforward.laws R h2 n nu m U V hU hV
    f hFImage hFLocal T hFlat).2 K hK).
- exact:((@CurrentFlatLipschitzPushforward.laws R h2 n nu m U V hU hV
    g hGImage hGLocal T hFlat).2 K hK).
Qed.

(** Source for [current_lipschitz_images_domain_agreement]:
    two independent local-image candidates agree when
    their maps agree on U, supporting the original
    endpoint identities of Federer 4.1.14, p. 371.
    A common scalar cutoff and the preceding global
    agreement suffice. Properness is needed only for
    f on spt T and is inherited by g. *)
Theorem current_lipschitz_images_domain_agreement
    (T:@current_space R h2 n U hU m)
    (hT:@is_locally_flat_current R h2 n m U hU T)
    (hProper:@is_current_proper_on_support R h2 n nu m U hU V T f hFImage)
    (Q P:@current_space R h2 nu V hV m):
  @is_current_lipschitz_image R h2 n nu m U V hU hV f hFImage hFLocal T Q->
  @is_current_lipschitz_image R h2 n nu m U V hU hV g hGImage hGLocal T P->Q = P.
Proof.
move=>hQ hP;apply:(@current_values_extensional R h2 nu m V hV)=>phi.
have[gamma hPlateau]:=@current_common_pushforward_cutoff R h2 n nu m
  U V hU hV f hFImage T T hProper hProper phi.
have hGammaF:@is_current_lipschitz_pushforward_cutoff R h2 n nu m U V hU hV
    T f phi gamma.
  move=>x hx hPhi;exact:hPlateau x (or_introl hx) hPhi.
have hGammaG:@is_current_lipschitz_pushforward_cutoff R h2 n nu m U V hU hV
    T g phi gamma.
  move=>x hx hPhi.
  rewrite -(hEqual x hx.1) in hPhi.
  exact:hPlateau x (or_introl hx) hPhi.
pose S:=@current_contraction R h2 n 0%N m U hU
  (smooth_test_inclusion (@current_smooth_space_laws R h2 n U hU 0%N) gamma) T.
pose hS:=@hT gamma.
have hAgreement:=@current_flat_lipschitz_pushforward_domain_agreement S hS.
have hQValue:=(proj2 hQ) phi gamma hS hGammaF.
have hPValue:=(proj2 hP) phi gamma hS hGammaG.
rewrite hAgreement in hQValue.
exact:(eq_trans hQValue (esym hPValue)).
Qed.

(** Source for [current_lipschitz_pushforward_domain_agreement]:
    the two opaque actual local images agree for
    maps equal on the original domain, supporting
    the endpoint identifications in Federer 4.1.14,
    p. 371. Arbitrary original properness evidence
    is accepted, without a normality or mass premise. *)
Theorem current_lipschitz_pushforward_domain_agreement
    (T:@current_space R h2 n U hU m)
    (hT:@is_locally_flat_current R h2 n m U hU T)
    (hProperF:@is_current_proper_on_support R h2 n nu m U hU V T f hFImage)
    (hProperG:@is_current_proper_on_support R h2 n nu m U hU V T g hGImage):
  @CurrentLipschitzPushforward.value R h2 n nu m U V hU hV
    f hFImage hFLocal T hT hProperF=
  @CurrentLipschitzPushforward.value R h2 n nu m U V hU hV
    g hGImage hGLocal T hT hProperG.
Proof.
exact:(@current_lipschitz_images_domain_agreement T hT hProperF _ _
  (@CurrentLipschitzPushforward.laws R h2 n nu m U V hU hV
    f hFImage hFLocal T hT hProperF)
  (@CurrentLipschitzPushforward.laws R h2 n nu m U V hU hV
    g hGImage hGLocal T hT hProperG)).
Qed.
End CurrentLipschitzMapDomainAgreement.
