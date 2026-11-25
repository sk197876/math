(** Federer (1969), 4.1.14, p. 370: the compact
    Lipschitz image has support contained in f(spt T),
    not merely in f(K). Keep the original flat index
    K throughout the defining approximation law. One such
    law gives a weak limit; smaller target neighbourhoods
    of f(spt T) are used only for eventual support. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormClassOneUP NormRegularity NormBoundedLinearTopology InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  FiniteCoordinates LipschitzUP OpenLocalLipschitzCompact SmoothCompactSet
  SmoothCompactImage SmoothCompactNeighbourhoods MetricOpenThickening
  MetricCompactNeighbourhood CurrentSpaces CurrentSupportGeometry
  CurrentCompactMapProper CurrentPushforwardSupport CurrentCompactPushforwardAlgebra
  CurrentOpenRestriction CurrentOpenRestrictionSupport CurrentFlatOpenRestriction
  FlatCurrentsUP FlatCurrentFinite CurrentLipschitzCompactImage
  CurrentCompactLipschitzPushforwardUP CurrentFlatSequenceLimits
  CurrentWeakSequenceLimit CurrentWeakEventualCompactSupport
  CurrentSmoothApproximationUP CurrentCompactSmoothApproximationUP
  CurrentCompactSmoothApproximationSealed CurrentCompactSmoothApproximationOriginal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentCompactLipschitzImageSupport.
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
Arguments hU : clear implicits.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Arguments hV : clear implicits.
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.
Hypothesis hLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U f.
Variable K:smooth_compact_set hNX U.
Variable T:@current_space R h2 n U hU m.
Hypothesis hFlat:@is_flat_current_supported_in R h2 n m U hU K T.
Variable Q:@current_space R h2 nu V hV m.
Hypothesis hCandidate:@is_current_compact_lipschitz_image R h2 n nu m
  U V hU hV f hImage hLocal K T Q.

(** Source for [current_compact_lipschitz_image_support]:
    spt(f#T) is contained in f(spt T), Federer
    4.1.14, p. 370. T is any original member
    of F_(m,K)(U), and Q is any candidate satisfying
    the independent original image law. No normality,
    finite mass or flat membership with index spt T
    is assumed. Empty supports and degree zero are included. *)
Theorem current_compact_lipschitz_image_support:
  @current_support R h2 nu V hV m Q `<=`
    f @` (@current_support R h2 n U hU m T).
Proof.
pose hCompactT:=@flat_supported_current_compact R h2 n m U hU K T hFlat.
pose KT:=@Build_smooth_compact_set R X NX hNX U
  (@current_support R h2 n U hU m T) (fun x hx=>hx.1) hCompactT.
pose J:=@current_lipschitz_compact_image R n nu U V hU f hImage hLocal KT.
pose fK:=@current_lipschitz_compact_image R n nu U V hU f hImage hLocal K.
have hLip:=@norm_open_local_lipschitz_compact R X Y NX NY hNX hNY U f
  (smooth_compact_carrier K) hU hLocal (smooth_compact_is_compact K)
  (smooth_compact_in_domain K).
have[L [hL hBoundK]]:=hLip.
pose hImageK:=fun x (hx:smooth_compact_carrier K x)=>
  hImage x (smooth_compact_in_domain K x hx).
pose data:=@CurrentCompactSmoothApproximation.value R n nu U V hU hV
  K f L hBoundK hImageK.
pose hApprox:=@CurrentCompactSmoothApproximation.laws R n nu U V hU hV
  K f L hBoundK hImageK.
pose Z:=data.1.
pose g:=data.2.
pose hZ:=current_compact_smooth_domain_open hApprox.
pose hKZ:=current_compact_smooth_domain_contains hApprox.
pose hZU:=@current_compact_smooth_domain_in_domain R n nu U V K f L Z g hApprox.
pose KZ:=@current_compact_index_in_open R n U Z K hKZ.
pose S:=@current_open_restriction R h2 n m Z U hZ hU hZU T.
have hSFlat:=@flat_current_open_restriction R h2 n m U Z hU hZ hZU K hKZ T hFlat.
pose hCompactS:=@flat_supported_current_compact R h2 n m Z hZ KZ S hSFlat.
have hG:=@current_compact_smooth_original_approximation R n nu
  U V K f L Z g hApprox.
pose P:=fun i=>@current_compact_map_pushforward R h2 n nu Z V hZ hV
  (g i) (current_smooth_approximation_image hG i)
  (current_smooth_approximation_class hG i) m S hCompactS.
have[E0 hInterior0]:=@smooth_compact_neighbourhood_exists R Y NY hNY nu
  (@coordinate_basis R nu) (@coordinate_basisP R nu) V hV fK.
have hInteriorK:forall x,smooth_compact_carrier K x->
    norm_domain_interior NY (smooth_compact_carrier E0) (f x).
  move=>x hx;apply:hInterior0;by exists x.
have hRecovery:=@flat_current_neighbourhood_inclusion_recovery R h2 n m
  U Z hU hZ hZU K hKZ T hFlat hCompactS.
have hLimit:=(proj2 hCandidate) E0 hInteriorK Z hZ hZU hKZ S hSFlat hRecovery g hG.
have hWeak:=@current_flat_sequence_limit_weak R h2 nu m V hV E0 P Q hLimit.
have hResult:@current_support R h2 nu V hV m Q `<=` smooth_compact_carrier J.
  apply:(@smooth_compact_neighbourhoods_detect_closed R Y NY hNY nu
    (@coordinate_basis R nu) (@coordinate_basisP R nu) V hV J
    (@current_support R h2 nu V hV m Q)).
  - move=>y hy;exact:hy.1.
  - move=>E hInterior.
    pose O:=@interior (real_norm_metric_space hNY) (smooth_compact_carrier E).
    have hJO:smooth_compact_carrier J `<=` O.
      move=>y hy.
      exact:((@norm_domain_interior_neighbourhood R Y NY hNY
        (smooth_compact_carrier E) y).1 (hInterior y hy)).
    have[r [hr hTube]]:=@compact_metric_open_thickening R
      (real_norm_metric_space hNY) (smooth_compact_carrier J) O
      (smooth_compact_is_compact J) (open_interior _) hJO.
    have[N hUniform]:=current_smooth_approximation_uniform hG hr.
    apply:(@current_weak_limit_eventual_support_compact R h2 nu m V hV E P Q N hWeak).
    move=>i hNi y hy.
    have[x hx <-]:=@current_pushforward_support_image R h2 n nu m Z V hZ hV
      S (g i) (current_smooth_approximation_image hG i)
      (current_smooth_approximation_class hG i)
      (@current_compact_map_proper R h2 n nu m Z V hZ S (g i)
        (current_smooth_approximation_image hG i)
        (norm_class_continuous (current_smooth_approximation_class hG i 0%N))
        hCompactS) y hy.
    have hxT:@current_support R h2 n U hU m T x.
      exact:(@current_open_restriction_support_subset R h2 n m Z U hZ hU hZU T x hx).
    have hxK:smooth_compact_carrier K x.
      exact:(@flat_current_supported_support R h2 n m U hU K T hFlat x hxT).
    have hFx:smooth_compact_carrier J (f x) by exists x.
    have hSmall:=hUniform i hNi x hxK.
    have hO:O (g i x).
      apply:hTube;exists (f x);first exact:hFx.
      change (is_true (NY (f x-g i x)<r)).
      by rewrite (real_seminorm_subtract hNY.1).
    exact:interior_subset hO.
exact:hResult.
Qed.
End CurrentCompactLipschitzImageSupport.
