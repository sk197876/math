(** Federer (1969), 4.1.23, pp. 379–380:
    a proper open coordinate box and
    its closed box have the same
    measure, and the latter is exactly
    its compact closure. Thus the
    chosen box closures stay in the
    prescribed open neighbourhood of C. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology ring.
From Federer Require Import RealNormUP NormMetric InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueHaar
  EuclideanDistributionMeasureContext EuclideanLebesgueDimensions EuclideanLebesgueBoxes
  EuclideanOpenCoordinateBoxUP EuclideanOpenCoordinateBoxMeasure
  EuclideanOpenBoxMeasurability SmoothCompactSet ClosedCoordinateBoxConvex
  FiniteMeasureSetDifference MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ClosedBoxGeometry.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation IT := (inner_metric_space (@euclidean_inner_productP R n)).
Variables a b : X.
Local Notation C := (@closed_coordinate_box R n a b).

(** Source for [closed_coordinate_box_norm_compact]:
    the actual closed rectangular index in
    Federer 4.1.23, p. 380,
    is compact in the original current
    norm topology. This holds even
    for unordered endpoints and dimension zero. *)
Theorem closed_coordinate_box_norm_compact : @compact XT C.
Proof.
have h := @euclidean_closed_box_compact R n a b.
have hImage := continuous_compact
  (continuous_subspaceT (@euclidean_distribution_inner_to_norm R n)) h.
change (@compact XT ((fun x : IT => (x:XT)) @` C)) in hImage.
by rewrite image_id in hImage.
Qed.

(** Source for [closed_coordinate_box_index]: the
    exact compact containing box used for
    the original F_A estimate of
    Federer 4.1.23, p. 380.
    Its carrier is the literal closed
    coordinate box; no enlarged support
    index or chosen point is introduced. *)
Definition closed_coordinate_box_index : smooth_compact_set hNX (fun _ : X => True) :=
  @Build_smooth_compact_set R X NX hNX (fun _ : X => True) C
    (fun _ _ => Logic.I) closed_coordinate_box_norm_compact.

(** Source for [proper_coordinate_box_closure]: the
    full closed rectangle is the actual
    closure of the selected proper open
    box, supporting the compact containment
    step in Federer 4.1.23,
    pp. 379–380. The empty-coordinate R^0
    box remains the whole one-point space. *)
Theorem proper_coordinate_box_closure (G : set X)
    (hG : @is_euclidean_open_coordinate_box R n a b G) :
  @closure XT G=C.
Proof.
have hClosed : @closed XT C := compact_closed (@metric_hausdorff R XT)
  closed_coordinate_box_norm_compact.
have hGC : G `<=` C.
  move=> x hx i; have /andP [hLow hHigh] := (hG.2 x).1 hx i.
  apply/andP; split; exact: ltW.
apply: funext=> x; apply: propext; split.
- move=> hx; apply: hClosed; exact: (@closureS XT G C hGC x hx).
- move=> hx W hW.
  have [r hr hBall] := (metricType_numDomainType.nbhs_mdistP (x:XT) W).1 hW.
  pose c : X := [ffun i => (a i+b i)/2].
  have hTwo : (0<(2:R)) by rewrite ltr0n.
  have hTwoNonzero : (2:R)!=0 := lt0r_neq0 hTwo.
  have hDouble (z : R) : z*2=z+z by ring.
  have hMiddle i : a i<c i<b i.
    rewrite /c ffunE; apply/andP; split.
    - rewrite ltr_pdivlMr // (hDouble (a i)) ltrD2l; exact: hG.1 i.
    - rewrite ltr_pdivrMr // (hDouble (b i)) ltrD2r; exact: hG.1 i.
  pose q := NX (c-x).
  have hQ : 0<=q := real_seminorm_nonnegative hNX.1 _.
  have hQOne : 0<q+1.
    apply: (lt_le_trans (@ltr01 R)); by rewrite lerDr.
  have hDenominator : 0<2*(q+1) := mulr_gt0 hTwo hQOne.
  pose t := Num.min (1/2) (r/(2*(q+1))).
  have hT : 0<t.
    rewrite /t lt_min; apply/andP; split.
    - exact: divr_gt0 (@ltr01 R) hTwo.
    - exact: divr_gt0 hr hDenominator.
  have hHalf : (1/2:R)<1.
    by rewrite ltr_pdivrMr // mul1r ltr1n.
  have hTFirst : t<=1/2 by rewrite /t ge_min lexx.
  have hTSecond : t<=r/(2*(q+1)) by rewrite /t ge_min lexx orbT.
  have hTOne : t<=1 := le_trans hTFirst (ltW hHalf).
  have hComplement : 0<=1-t by rewrite subr_ge0.
  pose z := x+t*:(c-x).
  have hGZ : G z.
    apply: (hG.2 z).2=> i.
    have /andP [hLow hHigh] := hx i.
    have /andP [hMiddleLow hMiddleHigh] := hMiddle i.
    have hCoordinate : z i=(1-t)*x i+t*c i.
      rewrite /z !ffunE.
      change ((x i:R)+t*((a i+b i)/2-(x i:R))=
        (1-t)*(x i:R)+t*((a i+b i)/2)).
      ring.
    have hConstant y : (1-t)*y+t*y=y by ring.
    rewrite hCoordinate; apply/andP; split.
    - rewrite -(hConstant (a i)).
      apply: ler_ltD; first exact: (ler_wpM2l hComplement hLow).
      by rewrite (ltr_pM2l hT).
    - rewrite -(hConstant (b i)).
      apply: ler_ltD; first exact: (ler_wpM2l hComplement hHigh).
      by rewrite (ltr_pM2l hT).
  have hDifference : z-x=t*:(c-x) by rewrite /z addrAC subrr add0r.
  have hFirst : t*q<t*(q+1).
    rewrite (ltr_pM2l hT) ltrDl; exact: ltr01.
  have hCap : t*(q+1)<=r/2.
    apply: (le_trans (ler_wpM2r (ltW hQOne) hTSecond)).
    have hDivision : r/(2*(q+1))*(q+1)=r/2.
      by rewrite invfM mulrA -mulrA (mulVf (lt0r_neq0 hQOne)) mulr1.
    by rewrite hDivision.
  have hRadiusHalf : r/2<r.
    by rewrite ltr_pdivrMr // (hDouble r) ltrDl.
  have hDistance : @mdist R XT x z<r.
    change (is_true (NX (x-z)<r)).
    rewrite (real_seminorm_subtract hNX.1 x z) hDifference
      (real_seminorm_scale hNX.1) (ger0_norm (ltW hT)).
    exact: lt_trans hFirst (le_lt_trans hCap hRadiusHalf).
  exists z; split; [exact: hGZ|exact: hBall z hDistance].
Qed.

(** Source for [proper_coordinate_box_null_boundary]:
    replacing a proper open box by
    its compact closure changes no
    Lebesgue characteristic current, supporting
    the rectangle construction of Federer
    4.1.23, pp. 379–380.
    Exact open and closed product volumes
    prove the actual omitted remainder null. *)
Theorem proper_coordinate_box_null_boundary (G : set X)
    (hG : @is_euclidean_open_coordinate_box R n a b G) :
  @euclidean_lebesgue_measure R n (C `\` G)=0%E.
Proof.
pose volume := \prod_(i:'I_n) (b i-a i).
have hContained : G `<=` C.
  move=> x hx i; have /andP [hLow hHigh] := (hG.2 x).1 hx i.
  apply/andP; split; exact: ltW.
have hOpen := @open_coordinate_box_volume R n a b G hG.
have hClosed := @euclidean_closed_box R n a b (fun i => ltW (hG.1 i)).
have h := @finite_measure_nested_difference R X (@euclidean_lebesgue_measure R n)
  (euclidean_lebesgue_is_measure R n) G C volume volume
  (@open_coordinate_box_measurable R n a b G hG) hContained hOpen hClosed.
by rewrite subrr in h.
Qed.
End ClosedBoxGeometry.
