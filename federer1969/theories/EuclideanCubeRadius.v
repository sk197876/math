(** Federer (1969), 2.10.39, printed p. 199: a box whose side lengths are at
    most h fits in a closed ball of diameter sqrt(n) h. Prove the coordinate
    square estimate and transfer it through the abstract orthonormal frame
    laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets lra.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerProductUP InnerNorm InnerMetric EuclideanLinearMaps OrthogonalMaps
  OrthogonalFinite OrthonormalFamilies EuclideanBoxUP MetricClosedBalls Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_coordinate_cube_norm_bound]: supporting
    sqrt(n) radius estimate in 2.10.39, p. 199.
    If every coordinate has absolute value at most r,
    the squared norm is at most n r squared.
    Ambient dimension zero and r zero are included. *)
Lemma euclidean_coordinate_cube_norm_bound (R : realType) n (x : R_n R n) (r : R) :
  0<=r -> (forall i, `|x i|<=r) ->
  inner_norm (@euclidean_inner_productP R n) x<=Num.sqrt n%:R*r.
Proof.
move=> hr hx.
have hs : (\sum_(i<n) (x i)^+2)<=\sum_(i<n) r^+2.
  apply: ler_sum=> i _.
  have hh : `|x i|^+2<=r^+2 by rewrite (ler_sqr (normr_ge0 _) hr); exact: hx.
  by rewrite real_normK ?num_real in hh.
rewrite -(ler_sqr (inner_norm_nonnegative _ x) (mulr_ge0 (sqrtr_ge0 _) hr))
  inner_norm_sqr exprMn sqr_sqrtr ?ler0n // /euclidean_inner_product.
have he : (\sum_(i<n) x i*x i)=\sum_(i<n) (x i)^+2.
  by apply: eq_bigr=> i _; rewrite expr2.
rewrite sumr_const card_ord -(@mulr_natl R (r^+2) n) in hs.
by rewrite he; exact hs.
Qed.

(** Source for [euclidean_frame_cube_norm_bound]: supporting
    orthogonal-coordinate version of the circumscribed-ball
    estimate in 2.10.39, p. 199. No particular
    orthonormal-basis construction is used. *)
Lemma euclidean_frame_cube_norm_bound (R : realType) n
    (e : 'I_n -> R_n R n) (x : R_n R n) (r : R) :
  orthonormal_family (@euclidean_inner_product R n) e -> 0<=r ->
  (forall i, `|euclidean_inner_product x (e i)|<=r) ->
  inner_norm (@euclidean_inner_productP R n) x<=Num.sqrt n%:R*r.
Proof.
move=> he hr hx.
pose f := euclidean_frame_map e.
have hf := euclidean_frame_orthogonal he.
have [z hz] := orthogonal_endomorphism_surjective (@euclidean_inner_productP R n)
  (@coordinate_basisP R n) hf x.
rewrite -hz (orthogonal_map_norm (@euclidean_inner_productP R n)
  (@euclidean_inner_productP R n) hf).
apply: (@euclidean_coordinate_cube_norm_bound R n z r hr)=> i.
have hh := hx i.
by rewrite -hz /f /= (euclidean_frame_inner he) in hh.
Qed.

(** Source for [euclidean_box_circumscribed_ball]: supporting
    closed ball of diameter sqrt(n) h containing
    each small box in 2.10.39, p. 199.
    Degenerate boxes and the zero-dimensional case are
    included; the radius need not be positive here. *)
Theorem euclidean_box_circumscribed_ball (R : realType) n origin e c Q (h : R) :
  @is_euclidean_rectangular_box R n origin e c Q ->
  0<=h -> (forall i, c i<=h) -> exists z,
    Q `<=` metric_closed_ball z (Num.sqrt n%:R*h/2).
Proof.
move=> hQ hh hc.
pose offset := euclidean_frame_map e ([ffun i=>c i/2] : R_n R n).
pose z := origin+offset.
exists z=> x hx.
have he := euclidean_box_orthonormal_law hQ.
have hcoord i : `|euclidean_inner_product (x-z) (e i)|<=h/2.
  have /andP [hlo hhi] := (proj1 (euclidean_box_carrier_law hQ x) hx) i.
  have hoff : euclidean_inner_product offset (e i)=c i/2.
    rewrite /offset /euclidean_frame_map /= (euclidean_frame_inner he).
    exact: ffunE.
  rewrite /z opprD addrA (bilBl (@euclidean_inner_bilinear R n)) hoff ler_norml.
  have hci := hc i.
  apply/andP; split; lra.
have hr : 0<=h/2 by lra.
have hbound := @euclidean_frame_cube_norm_bound R n e (x-z) (h/2) he hr hcoord.
change (is_true (inner_norm (@euclidean_inner_productP R n) (z-x)<=Num.sqrt n%:R*h/2)).
rewrite -[z-x]opprB inner_normN.
by rewrite mulrA in hbound.
Qed.
