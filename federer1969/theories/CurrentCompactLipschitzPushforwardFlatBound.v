(** Federer (1969), 4.1.14, pp. 370–371:
    the actual image flat value is bounded
    by max(Lip(f|K)^m,Lip(f|K)^(m+1)) times F_K(T).
    Transport the already proved opaque carrier-map
    estimate through the exact original inclusions;
    no representation of the current is chosen
    in the public statement. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP LipschitzConstant SmoothCompactSet CurrentSpaces FlatCurrentsUP
  CurrentFlatNorm FlatCurrentSpaces LinearSubspaceRepresentationUP
  CurrentLipschitzCompactImage CurrentLipschitzFlatCoefficient
  CurrentCompactLipschitzPushforwardSealed CurrentFlatLipschitzPushforwardSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCompactLipschitzPushforwardFlatBound.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Hypothesis hLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U f.
Variable K:smooth_compact_set hNX U.
Local Notation fK:=(@current_lipschitz_compact_image R n nu U V hU f hImage hLocal K).
Variable L:R.
Hypothesis hLeast:@is_least_metric_lipschitz_constant R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY)
  (smooth_compact_carrier K) f L.

(** Source for [current_compact_lipschitz_pushforward_flat_bound]:
    the displayed original F_(fK) estimate,
    Federer 4.1.14, pp. 370–371. Every
    fixed-K flat current is admitted; no
    normality or finite-mass premise is needed. *)
Theorem current_compact_lipschitz_pushforward_flat_bound
    (T:@current_space R h2 n U hU m)
    (hT:@is_flat_current_supported_in R h2 n m U hU K T):
  (@current_flat_norm R h2 nu m V hV fK
    (@CurrentCompactLipschitzPushforward.value R h2 n nu m U V hU hV
      f hImage hLocal K T hT) <=
    (current_lipschitz_flat_coefficient m L)%:E*
      @current_flat_norm R h2 n m U hU K T)%E.
Proof.
have[z hZ]:=subspace_representation_full (@flat_current_space_laws R h2 n m U hU K) hT.
subst T.
rewrite (@CurrentCompactLipschitzPushforward.value_map R h2 n nu m U V hU hV
  f hImage hLocal K z hT) !flat_current_norm_value -EFinM lee_fin.
exact:(@CurrentCompactLipschitzPushforward.map_bound R h2 n nu m U V hU hV
  f hImage hLocal K L hLeast z).
Qed.

(** Source for [current_flat_lipschitz_pushforward_flat_bound]:
    the same exact F_K estimate for the
    original compact-index union image, Federer
    4.1.14, pp. 370–371. The chosen index
    of the opaque union image is irrelevant. *)
Theorem current_flat_lipschitz_pushforward_flat_bound
    (T:@current_space R h2 n U hU m)
    (hGlobal:@is_flat_current R h2 n m U hU T)
    (hT:@is_flat_current_supported_in R h2 n m U hU K T):
  (@current_flat_norm R h2 nu m V hV fK
    (@CurrentFlatLipschitzPushforward.value R h2 n nu m U V hU hV
      f hImage hLocal T hGlobal) <=
    (current_lipschitz_flat_coefficient m L)%:E*
      @current_flat_norm R h2 n m U hU K T)%E.
Proof.
rewrite (@CurrentFlatLipschitzPushforward.compact_value R h2 n nu m U V hU hV
  f hImage hLocal T hGlobal K hT).
exact:current_compact_lipschitz_pushforward_flat_bound.
Qed.
End CurrentCompactLipschitzPushforwardFlatBound.
