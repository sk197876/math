(** Federer (1969), 4.1.14, p. 371: changing
    the open time/source neighbourhood leaves the actual
    compact Lipschitz image of the interval product unchanged.
    Use the exact product restriction and the original
    source-neighbourhood law; no support-coincidence theorem
    from 4.1.15 is used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanOneCoordinate EuclideanBlockLinearMaps EuclideanCartesianMap
  LipschitzUP CurrentSpaces CurrentOpenRestriction FlatCurrentsUP
  CurrentCartesianDomain CurrentCartesianProductSealed CurrentCartesianSupportEquality
  CurrentHomotopyUP CurrentHomotopyGeometry CurrentHomotopyDomain
  CurrentHomotopyTimeSegment CurrentTimeProductNeighbourhood
  CurrentApproximationOpenRestriction CurrentFlatLipschitzPushforwardSealed
  CurrentFlatLipschitzPushforwardBasic CurrentFlatLipschitzProofIndependence
  CurrentFlatLipschitzSourceNeighbourhood.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentFlatTimeProductImageNeighbourhood.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n nu m : nat.
Variables A B : set R.
Variables U W : set (R_n R n).
Variable V : set (R_n R nu).
Hypothesis hA : @is_homotopy_parameter_interval R A.
Hypothesis hB : @is_homotopy_parameter_interval R B.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation Z := (R_n R (1+n)%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N)).
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Hypothesis hW : forall x, W x -> norm_domain_interior NX W x.
Hypothesis hV : forall y, V y -> norm_domain_interior NY V y.
Hypothesis hBA : forall t, B t -> A t.
Hypothesis hWU : forall x, W x -> U x.
Local Notation AT := (@current_homotopy_time_domain R A).
Local Notation BT := (@current_homotopy_time_domain R B).
Local Notation hAT := (@current_homotopy_time_domain_open R A hA).
Local Notation hBT := (@current_homotopy_time_domain_open R B hB).
Local Notation AU := (@current_homotopy_product_domain R n A U).
Local Notation BW := (@current_homotopy_product_domain R n B W).
Local Notation hAU := (@current_cartesian_domain_open R 1%N n AT U hAT hU).
Local Notation hBW := (@current_cartesian_domain_open R 1%N n BT W hBT hW).
Let hBWAU : forall z, BW z -> AU z :=
  fun z hz => conj (@hBA _ hz.1) (@hWU _ hz.2).
Variable h : Z -> Y.
Hypotheses (hImageA : forall z, AU z -> V (h z))
  (hImageB : forall z, BW z -> V (h z)).
Hypotheses (hLocalA : @is_locally_metric_lipschitz R
    (real_norm_metric_space hNZ) (real_norm_metric_space hNY) AU h)
  (hLocalB : @is_locally_metric_lipschitz R
    (real_norm_metric_space hNZ) (real_norm_metric_space hNY) BW h).
Variable T : @current_space R h2 n U hU m.
Hypothesis hCompact : @compact (real_norm_metric_space hNX)
  (@current_support R h2 n U hU m T).
Hypothesis hSupportW : @current_support R h2 n U hU m T `<=` W.
Local Notation S := (@current_open_restriction R h2 n m W U hW hU hWU T).
Local Notation TimeA := (@current_homotopy_time_segment R A hA h2).
Local Notation TimeB := (@current_homotopy_time_segment R B hB h2).
Local Notation Large := (@CartesianCurrentProduct.value R h2 1%N n 1%N m
  AT U hAT hU TimeA T).
Local Notation Small := (@CartesianCurrentProduct.value R h2 1%N n 1%N m
  BT W hBT hW TimeB S).
Hypothesis hLargeFlat : @is_flat_current R h2 (1+n)%N (1+m)%N AU hAU Large.
Hypothesis hSmallFlat : @is_flat_current R h2 (1+n)%N (1+m)%N BW hBW Small.

(** Source for [current_flat_time_product_image_neighbourhood]:
    the actual compact flat homotopy image is independent
    of a smaller original open time/source neighbourhood,
    Federer 4.1.14, p. 371. The supplied flat membership
    concerns the actual products, never a support-sized flat index. *)
Theorem current_flat_time_product_image_neighbourhood :
  @CurrentFlatLipschitzPushforward.value R h2 (1+n)%N nu (1+m)%N
    AU V hAU hV h hImageA hLocalA Large hLargeFlat=
  @CurrentFlatLipschitzPushforward.value R h2 (1+n)%N nu (1+m)%N
    BW V hBW hV h hImageB hLocalB Small hSmallFlat.
Proof.
have hSupport : @current_support R h2 (1+n)%N AU hAU (1+m)%N Large `<=` BW.
  move=> z hz.
  rewrite (@current_cartesian_support R h2 1%N n 1%N m AT U hAT hU TimeA T) in hz.
  change (@current_support R h2 1%N AT hAT 1%N TimeA
      (@euclidean_first_block_map R 1%N n z) /\
    @current_support R h2 n U hU m T
      (@euclidean_last_block_map R 1%N n z)) in hz.
  split.
  - exact: (@current_homotopy_closed_time_band R B hB _
      (@current_homotopy_time_segment_support R A hA h2 _ hz.1)).
  - exact: @hSupportW _ hz.2.
pose Restricted := @current_open_restriction R h2 (1+n)%N (1+m)%N
  BW AU hBW hAU hBWAU Large.
have hRestriction : Restricted=Small := @current_time_product_neighbourhood_restriction
  R h2 n m A B U W hA hB hU hW hBA hWU T hCompact hSupportW.
have hRestrictedFlat : @is_flat_current R h2 (1+n)%N (1+m)%N BW hBW Restricted.
  by rewrite hRestriction.
pose hImageRestricted := fun z (hz:BW z) => @hImageA z (@hBWAU z hz).
pose hLocalRestricted := @metric_local_lipschitz_domain_restriction R
  (real_norm_metric_space hNZ) (real_norm_metric_space hNY) AU BW h hBWAU hLocalA.
have hFirst := @current_flat_lipschitz_pushforward_open_restriction R h2
  (1+n)%N nu (1+m)%N AU BW V hAU hBW hV hBWAU h hImageA hLocalA
  Large hLargeFlat hSupport hRestrictedFlat.
have hSecond := @current_flat_lipschitz_pushforward_data_independent R h2
  (1+n)%N nu (1+m)%N BW V hBW hV h hImageRestricted hImageB
  hLocalRestricted hLocalB Restricted hRestrictedFlat hRestrictedFlat.
have hThird := @current_flat_lipschitz_pushforward_congruence R h2
  (1+n)%N nu (1+m)%N BW V hBW hV h hImageB hLocalB
  Restricted Small hRestrictedFlat hSmallFlat hRestriction.
exact: eq_trans hFirst (eq_trans hSecond hThird).
Qed.
End CurrentFlatTimeProductImageNeighbourhood.
