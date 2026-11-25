(** Federer (1969), 4.1.14, p. 370: the normal-current
    image has exactly the compact image index f(K), and
    every allowed smooth family gives that same image in
    every prescribed F_E. Compact neighbourhoods are used
    only to prove existence and convergence; they do not
    replace the original target support index. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormRegularity InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct FiniteCoordinates LipschitzUP OpenLocalLipschitzCompact
  CurrentSpaces SmoothCompactSet SmoothCompactNeighbourhoods NormalCurrentsUP
  CurrentCompactPushforwardAlgebra CurrentLipschitzCompactImage
  CurrentSmoothApproximationUP CurrentFlatSequenceLimitUP CurrentFlatSequenceLimits
  CurrentFlatSequenceComparison CurrentWeakSequenceLimit
  CurrentNormalSmoothApproximationCauchy CurrentNormalSmoothApproximationLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentNormalSmoothApproximationImage.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (Z:set X) (V:set Y).
Hypothesis hZ:forall x,Z x->norm_domain_interior NX Z x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variable K:smooth_compact_set hNX Z.
Variable f:X->Y.
Hypothesis hImage:forall x,Z x->V (f x).
Hypothesis hLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) Z f.
Local Notation fK:=(@current_lipschitz_compact_image R n nu Z V hZ f hImage hLocal K).
Variable g:nat->X->Y.
Hypothesis hG:@is_current_smooth_approximation R n nu Z V K f g.
Variable T:@current_space R h2 n Z hZ m.
Hypothesis hNormal:@is_normal_current R h2 n Z hZ m T.
Hypothesis hSupport:@current_support R h2 n Z hZ m T `<=` smooth_compact_carrier K.
Arguments hSupport : clear implicits.
Local Notation u:=(fun i=>@current_compact_map_pushforward R h2 n nu Z V hZ hV
  (g i) (current_smooth_approximation_image hG i)
  (current_smooth_approximation_class hG i) m T hNormal.2).
Local Notation support:=(@current_support R h2 nu V hV m).

(** Source for [current_normal_smooth_approximation_image]: the
    normal-current construction and its independence of the
    smooth family and compact E, Federer 4.1.14, p. 370.
    The two sequences are compared in their original F_E;
    no global derivative bound or target convexity is added. *)
Theorem current_normal_smooth_approximation_image:
  exists Q:@current_space R h2 nu V hV m,
    @normal_currents_supported_in R h2 nu V hV m fK Q /\
    forall (q:nat->X->Y)
      (hQ:@is_current_smooth_approximation R n nu Z V K f q)
      (E:smooth_compact_set hNY V),
      (forall x,smooth_compact_carrier K x->
        norm_domain_interior NY (smooth_compact_carrier E) (f x))->
      @is_current_flat_sequence_limit R h2 nu m V hV E
        (fun i=>@current_compact_map_pushforward R h2 n nu Z V hZ hV
          (q i) (current_smooth_approximation_image hQ i)
          (current_smooth_approximation_class hQ i) m T hNormal.2) Q.
Proof.
pose hf:=@norm_open_local_lipschitz_class_zero R X Y NX NY hNX hNY Z f hZ hLocal.
have[E0 hE0]:=@smooth_compact_neighbourhood_exists R Y NY hNY nu
  (@coordinate_basis R nu) (@coordinate_basisP R nu) V hV fK.
have hInside0 x (hx:smooth_compact_carrier K x):
    norm_domain_interior NY (smooth_compact_carrier E0) (f x).
  apply:hE0;by exists x.
have[Q [hNormalQ hLimit0]]:=@current_normal_smooth_approximation_limit
  R h2 n nu m Z V hZ hV K f hImage hf g hG T hNormal hSupport E0 hInside0.
have hLimitEvery (E:smooth_compact_set hNY V)
    (hInside:forall x,smooth_compact_carrier K x->
      norm_domain_interior NY (smooth_compact_carrier E) (f x)):
    @is_current_flat_sequence_limit R h2 nu m V hV E u Q.
  have[P [hP hLimit]]:=@current_normal_smooth_approximation_limit
    R h2 n nu m Z V hZ hV K f hImage hf g hG T hNormal hSupport E hInside.
  have hEquality:Q = P.
    exact:(@current_weak_sequence_limit_unique R h2 nu m V hV u Q P
      (@current_flat_sequence_limit_weak R h2 nu m V hV E0 u Q hLimit0)
      (@current_flat_sequence_limit_weak R h2 nu m V hV E u P hLimit)).
  by rewrite hEquality.
have hExactSupport:support Q `<=` smooth_compact_carrier fK.
  apply:(@smooth_compact_neighbourhoods_detect_closed R Y NY hNY nu
    (@coordinate_basis R nu) (@coordinate_basisP R nu) V hV fK (support Q)).
  - by move=>y hy;exact:hy.1.
  move=>E hInside.
  have hInsideK x (hx:smooth_compact_carrier K x):
      norm_domain_interior NY (smooth_compact_carrier E) (f x).
    apply:hInside;by exists x.
  have[P [hP hLimit]]:=@current_normal_smooth_approximation_limit
    R h2 n nu m Z V hZ hV K f hImage hf g hG T hNormal hSupport E hInsideK.
  have hEquality:Q = P.
    exact:(@current_weak_sequence_limit_unique R h2 nu m V hV u Q P
      (@current_flat_sequence_limit_weak R h2 nu m V hV E0 u Q hLimit0)
      (@current_flat_sequence_limit_weak R h2 nu m V hV E u P hLimit)).
  by rewrite hEquality;exact:hP.2.
exists Q;split;first by split;[exact:hNormalQ.1|exact:hExactSupport].
move=>q hQ E hInside.
apply:(@current_flat_sequence_limit_compare R h2 nu m V hV E u
  (fun i=>@current_compact_map_pushforward R h2 n nu Z V hZ hV
    (q i) (current_smooth_approximation_image hQ i)
    (current_smooth_approximation_class hQ i) m T hNormal.2) Q
  (hLimitEvery E hInside)).
move=>epsilon hEpsilon.
have[N hN]:=@current_normal_smooth_approximations_compare R h2 n nu Z V hZ hV
  K f hImage hf q g hQ hG m T hNormal hSupport E hInside epsilon hEpsilon.
exists N=>j hNj;exact:(@hN j j hNj hNj).
Qed.
End CurrentNormalSmoothApproximationImage.
