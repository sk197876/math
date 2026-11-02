(** Federer (1969), 3.2.33, p. 270: a constant
    rank-mu neighbourhood has a positive H^(m-mu) fibre.
    The erratum p. 5, book p. 270 line 28,
    corrects the reference to 3.1.18. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness RealNormUP NormDifferentialUP NormClassOneUP NormClassOneLinearPostcompose
  NormRegularity NormFiniteLinearBound NormDiffeomorphismUP EuclideanBlockLinearMaps EuclideanProductBox
  ConstantRankChartUP ConstantRankTheorem NormRankZero ClassOneDomainNullImage
  EuclideanOpenPositiveMass EuclideanHausdorffLebesgue MetricClosedBalls
  HausdorffMeasure MeasureUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section PositiveFibre.
Variable R:realType.
Variables mu l v:nat.
Local Notation X:=(R_n R (mu+l)).
Local Notation Y:=(R_n R v).
Local Notation Z:=(R_n R l).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R (mu+l))).
Local Notation NZ:=(inner_norm (@euclidean_inner_productP R l)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R (mu+l))).
Local Notation hNZ:=(inner_norm_real_norm (@euclidean_inner_productP R l)).
Local Notation r:=(@euclidean_first_block_map R mu l).
Local Notation q:=(@euclidean_last_block_map R mu l).
Local Notation i:=(@euclidean_first_injection_map R mu l).
Local Notation j:=(@euclidean_last_injection_map R mu l).

(** Source for [constant_rank_chart_fibre_nonnull]: the
    positive fibre claim in Federer 3.2.33, p. 270,
    using the actual product source chart of 3.1.18,
    pp. 229–230. The last coordinate of g maps
    this fibre onto a nonempty open l-ball. Its actual
    class-one local bounds preclude a Hausdorff-null fibre.
    Every natural l, including zero, is retained. *)
Theorem constant_rank_chart_fibre_nonnull (A U:set X) (f:X->Y)
    (D:X->Hom X Y) a e p k g G psi:
  @is_euclidean_constant_rank_chart R mu l v 1%N A f D a U e p k g G psi ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (mu+l))) l
    [set x|A x /\f x=f a]<>0%E.
Proof.
move=>hC hNull.
pose hSource:=constant_rank_source_chart hC.
have he:=constant_rank_radius_positive hC.
have [Dg hDg]:=(norm_class_firstP hNX hNX U g).1
  (norm_diffeomorphism_forward_class hSource).
have hQ:=@norm_finite_linear_bounded R X Z NX NZ hNX hNZ (mu+l)
  (@coordinate_basis R (mu+l)) (@coordinate_basisP R (mu+l)) q.
have hProjected:norm_class_one NX NZ U (fun x=>q (g x)).
  exists (fun x=>hom_comp q (Dg x)).
  exact:(norm_class_one_linear_postcompose hNX hNZ hDg hQ).
pose E:set X:=[set x|U x /\f x=f a].
pose H:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (mu+l))) l.
have hE:H E=0%E.
  apply:(measure_null_subset (@hausdorff_measure_is_measure R
    (inner_metric_space (@euclidean_inner_productP R (mu+l))) l) _ hNull)=>x [hx hf].
  split; first exact:(@constant_rank_domain_subset R mu l v 1%N A f D a U e p k g G psi hC x hx).
  exact hf.
have hImageNull:=@class_one_domain_hausdorff_null_image R (mu+l) l l U E
  (fun x=>q (g x)) hProjected (fun x hx=>hx.1) hE.
pose B:set (inner_metric_space (@euclidean_inner_productP R l)):=
  [set w|mdist (q (g a):inner_metric_space (@euclidean_inner_productP R l)) w<e].
have hBopen:open B by exact:metric_open_ball_open.
have hBpoint:B (q (g a)).
  change (is_true (NZ (q (g a)-q (g a))<e)).
  by rewrite subrr inner_norm0.
have hSubset:B `<=` (fun x=>q (g x)) @` E.
  move=>w hw.
  pose z:=i (r (g a))+j w.
  have hBox:@euclidean_product_box R mu l (g a) e z.
    apply:(euclidean_product_box_coordinates (g a) e (r (g a)) w).2.
    split; first by rewrite subrr inner_norm0.
    change (is_true (NZ (q (g a)-w)<e)) in hw.
    by rewrite -[q (g a)-w]opprB inner_normN in hw.
  have hxU:U (G z):=norm_diffeomorphism_inverse_maps hSource hBox.
  have hInverse:g (G z)=z:=norm_diffeomorphism_right_inverse hSource hBox.
  have hValue:f (G z)=f a.
    rewrite (constant_rank_section_factor hC hxU)
      -(constant_rank_source_prefix hC hxU) hInverse /z linearD /=
      euclidean_first_block_injectionK euclidean_first_block_last_injection addr0.
    exact:constant_rank_section_base hC.
  exists (G z); first by split.
  rewrite hInverse /z linearD /= euclidean_last_block_first_injection
    euclidean_last_block_injectionK add0r; reflexivity.
have hBNull:=measure_null_subset (@hausdorff_measure_is_measure R
  (inner_metric_space (@euclidean_inner_productP R l)) l) hSubset hImageNull.
rewrite (euclidean_hausdorff_spherical_lebesgue B).1 in hBNull.
have hPositive:=euclidean_open_positive_mass hBopen hBpoint.
by rewrite hBNull ltxx in hPositive.
Qed.

(** Source for [constant_rank_fibre_nonnull]: the corrected
    3.1.18 appeal in Federer 3.2.33, p. 270.
    The constant-rank chart and its nonnull fibre are
    proved from the actual class-one differential and generic
    rank hypothesis; no chart or fibre positivity is assumed. *)
Theorem constant_rank_fibre_nonnull (A:set X) (f:X->Y) (D:X->Hom X Y) a:
  is_norm_class_one_field NX (inner_norm (@euclidean_inner_productP R v)) A f D ->
  norm_generic_rank NX A D a mu ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (mu+l))) l
    [set x|A x /\f x=f a]<>0%E.
Proof.
move=>hD hGeneric.
have hClass:norm_class hNX (inner_norm_real_norm (@euclidean_inner_productP R v)) A f 1%N.
  apply:(norm_class_firstP hNX (inner_norm_real_norm (@euclidean_inner_productP R v)) A f).2.
  by exists D.
have [U [e [p [k [g [G [psi hC]]]]]]]:=@federer_3_1_18 R mu l v A f D a 1%N
  (leqnn 1) hClass hD hGeneric.
exact:(constant_rank_chart_fibre_nonnull hC).
Qed.
End PositiveFibre.
