(** Federer (1969), 4.1.14, p. 371: the
    original compact flat image satisfies (g composed f)#T
    =g#(f#T). Compatible smoothing families and their
    intermediate source are derived internally. Neither
    normality nor finite mass is required of T. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP MetricLocalLipschitzComposition SmoothCompactSet
  CurrentSpaces CurrentOpenRestriction CurrentSupportGeometry FlatCurrentsUP
  FlatCurrentFinite CurrentFlatCompactMonotone CurrentLipschitzCompactImage
  CurrentApproximationOpenRestriction CurrentFlatOpenRestriction
  CurrentCompactSmoothApproximationUP CurrentCompactSmoothApproximationOriginal
  CurrentNestedSmoothDomainRefinement CurrentCompactLipschitzCompositionLimit
  CurrentFlatLipschitzPushforwardSealed CurrentFlatLipschitzPushforwardBasic
  CurrentFlatLipschitzProofIndependence CurrentFlatLipschitzSourceNeighbourhood
  CurrentFlatLipschitzTargetNeighbourhood.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentFlatLipschitzComposition.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n nu omega m : nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation Z := (R_n R omega).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R omega)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R omega)).
Variables (U : set X) (V : set Y) (W : set Z).
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Hypothesis hV : forall y, V y -> norm_domain_interior NY V y.
Hypothesis hW : forall z, W z -> norm_domain_interior NZ W z.
Variables (f : X -> Y) (g : Y -> Z).
Hypothesis hFImage : forall x, U x -> V (f x).
Hypothesis hGImage : forall y, V y -> W (g y).
Hypothesis hFLocal : @is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U f.
Hypothesis hGLocal : @is_locally_metric_lipschitz R
  (real_norm_metric_space hNY) (real_norm_metric_space hNZ) V g.
Local Notation gf := (fun x => g (f x)).
Let hGFImage : forall x, U x -> W (gf x) :=
  fun x hx => @hGImage (f x) (@hFImage x hx).
Let hGFLocal := @metric_local_lipschitz_composition R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY)
  (real_norm_metric_space hNZ) U V f g hFImage hFLocal hGLocal.
Local Notation F := (@CurrentFlatLipschitzPushforward.value R h2 n nu m
  U V hU hV f hFImage hFLocal).
Local Notation G := (@CurrentFlatLipschitzPushforward.value R h2 nu omega m
  V W hV hW g hGImage hGLocal).
Local Notation GF := (@CurrentFlatLipschitzPushforward.value R h2 n omega m
  U W hU hW gf hGFImage hGFLocal).

(** Source for [current_flat_lipschitz_pushforward_composition]:
    exactly (g composed f)#T=g#(f#T) on the original
    compact flat space, Federer 4.1.14, p. 371.
    Every auxiliary compact, domain and smooth family is
    proved to exist internally. The target is an arbitrary
    open set and all zero and empty cases are retained. *)
Theorem current_flat_lipschitz_pushforward_composition
    (T : @current_space R h2 n U hU m)
    (hFlat : @is_flat_current R h2 n m U hU T) :
  GF T hFlat=G (F T hFlat)
    (proj1 (@CurrentFlatLipschitzPushforward.laws R h2 n nu m U V hU hV
      f hFImage hFLocal T hFlat)).
Proof.
have [K hKT] := hFlat.
have [E [Lg [Zg [b [Zf [a [hKZf hData]]]]]]] :=
  @current_nested_smooth_domain_refinement_exists R n nu omega U V W
    hU hV hW f g hFImage hGImage hFLocal hGLocal K.
have [hZf [hZfU [hFZg [_ [hInside [hB [hA hAB]]]]]]] := hData.
pose hZg := current_compact_smooth_domain_open hB.
pose hZgV := @current_compact_smooth_domain_in_domain R nu omega V W
  E g Lg Zg b hB.
pose hEZg := current_compact_smooth_domain_contains hB.
pose KS := @current_compact_index_in_open R n U Zf K hKZf.
pose ES := @current_compact_index_in_open R nu V Zg E hEZg.
pose Source := @current_open_restriction R h2 n m Zf U hZf hU hZfU T.
pose hSourceK := @flat_current_open_restriction R h2 n m U Zf hU hZf hZfU
  K hKZf T hKT.
have hSource : @is_flat_current R h2 n m Zf hZf Source by exists KS.
have hTInside : @current_support R h2 n U hU m T `<=` Zf.
  move=> x hx; exact: hKZf x
    (@flat_current_supported_support R h2 n m U hU K T hKT x hx).
pose hFSmallV := fun x (hx:Zf x) => @hFImage x (hZfU x hx).
pose hFSmallLocal := @metric_local_lipschitz_domain_restriction R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U Zf f hZfU hFLocal.
pose hGSmall := fun y (hy:Zg y) => @hGImage y (hZgV y hy).
pose hGSmallLocal := @metric_local_lipschitz_domain_restriction R
  (real_norm_metric_space hNY) (real_norm_metric_space hNZ) V Zg g hZgV hGLocal.
pose Q := F T hFlat.
pose QV := @CurrentFlatLipschitzPushforward.value R h2 n nu m Zf V hZf hV
  f hFSmallV hFSmallLocal Source hSource.
pose QS := @CurrentFlatLipschitzPushforward.value R h2 n nu m Zf Zg hZf hZg
  f hFZg hFSmallLocal Source hSource.
pose hQ := proj1 (@CurrentFlatLipschitzPushforward.laws R h2 n nu m U V hU hV
  f hFImage hFLocal T hFlat).
pose hQS := proj1 (@CurrentFlatLipschitzPushforward.laws R h2 n nu m Zf Zg hZf hZg
  f hFZg hFSmallLocal Source hSource).
have hSourceF : Q=QV := @current_flat_lipschitz_pushforward_open_restriction
  R h2 n nu m U Zf V hU hZf hV hZfU f hFImage hFLocal
  T hFlat hTInside hSource.
pose RestrictQ := @current_open_restriction R h2 nu m Zg V hZg hV hZgV Q.
have hRestrictQ : RestrictQ=QS.
  rewrite /RestrictQ hSourceF.
  exact: (@current_flat_lipschitz_target_neighbourhood_restriction
    R h2 n nu m Zf Zg V hZf hZg hV f hFZg hFSmallV hZgV
    hFSmallLocal Source hSource).
have hRestrictedFlat : @is_flat_current R h2 nu m Zg hZg RestrictQ.
  by rewrite hRestrictQ.
have hQInside : @current_support R h2 nu V hV m Q `<=` Zg.
  move=> y hy.
  have [x hx <-] := @current_flat_lipschitz_pushforward_support R h2 n nu m
    U V hU hV f hFImage hFLocal T hFlat y hy.
  exact: hFZg x (hTInside x hx).
pose RS := @CurrentFlatLipschitzPushforward.value R h2 nu omega m Zg W hZg hW
  g hGSmall hGSmallLocal QS hQS.
have hSourceG : G Q hQ=RS.
  have hFirst := @current_flat_lipschitz_pushforward_open_restriction
    R h2 nu omega m V Zg W hV hZg hW hZgV g hGImage hGLocal
    Q hQ hQInside hRestrictedFlat.
  have hSecond := @current_flat_lipschitz_pushforward_congruence R h2 nu omega m
    Zg W hZg hW g hGSmall hGSmallLocal RestrictQ QS hRestrictedFlat hQS hRestrictQ.
  exact: eq_trans hFirst hSecond.
pose hGFSmallImage := fun x (hx:Zf x) => @hGFImage x (hZfU x hx).
pose hGFSmallLocal := @metric_local_lipschitz_domain_restriction R
  (real_norm_metric_space hNX) (real_norm_metric_space hNZ) U Zf gf hZfU hGFLocal.
pose hGFCoreImage := fun x (hx:Zf x) => hGSmall (f x) (hFZg x hx).
pose hGFCoreLocal := @metric_local_lipschitz_composition R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY)
  (real_norm_metric_space hNZ) Zf Zg f g hFZg hFSmallLocal hGSmallLocal.
pose PS := @CurrentFlatLipschitzPushforward.value R h2 n omega m Zf W hZf hW
  gf hGFCoreImage hGFCoreLocal Source hSource.
have hSourceGF : GF T hFlat=PS.
  have hFirst := @current_flat_lipschitz_pushforward_open_restriction
    R h2 n omega m U Zf W hU hZf hW hZfU gf hGFImage hGFLocal
    T hFlat hTInside hSource.
  have hSecond := @current_flat_lipschitz_pushforward_data_independent R h2 n omega m
    Zf W hZf hW gf hGFSmallImage hGFCoreImage hGFSmallLocal hGFCoreLocal
    Source hSource hSource.
  exact: eq_trans hFirst hSecond.
have hQFixed := (@CurrentFlatLipschitzPushforward.laws R h2 n nu m Zf Zg hZf hZg
  f hFZg hFSmallLocal Source hSource).2 KS hSourceK.
pose fKS := @current_lipschitz_compact_image R n nu Zf Zg hZf
  f hFZg hFSmallLocal KS.
have hIndex : smooth_compact_carrier fKS `<=` smooth_compact_carrier ES.
  move=> y [x hx <-].
  exact: (@norm_domain_interior_member R Y NY hNY
    (smooth_compact_carrier E) (f x) (hInside x hx)).
have hQES := @flat_current_compact_monotone R h2 nu m Zg hZg fKS ES
  hIndex QS hQFixed.1.
have hRFixed := (@CurrentFlatLipschitzPushforward.laws R h2 nu omega m Zg W hZg hW
  g hGSmall hGSmallLocal QS hQS).2 ES hQES.
have hPFixed := (@CurrentFlatLipschitzPushforward.laws R h2 n omega m Zf W hZf hW
  gf hGFCoreImage hGFCoreLocal Source hSource).2 KS hSourceK.
have hBOriginal := @current_compact_smooth_original_approximation R nu omega V W
  E g Lg Zg b hB.
have hSmall := @current_compact_lipschitz_composition_limit R h2 n nu omega m
  Zf Zg W hZf hZg hW f g hFZg hGSmall hFSmallLocal hGSmallLocal
  KS ES hInside Source hSourceK QS hQFixed PS RS hPFixed hRFixed
  a b hA hBOriginal hAB.
exact: eq_trans hSourceGF (eq_trans hSmall (esym hSourceG)).
Qed.
End CurrentFlatLipschitzComposition.
