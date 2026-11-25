(** Federer (1969), 4.1.14, pp. 371–372: preserve
    an arbitrary open target while approximating the two
    endpoints of the original affine deformation. Compactness
    gives one source neighbourhood, one bounded open time
    interval and one positive target margin. The segment
    hypothesis is required only over the original compact K. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals topology num_normedtype normed_module lra.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormClassOneUP NormClassHigherRestriction NormRegularity NormBoundedLinearTopology
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct EuclideanOneCoordinate EuclideanBlockCoordinates
  EuclideanBlockLinearMaps EuclideanCartesianMap CurrentCartesianCompact
  ScalarCurrentIntervalCompact RealMetricBackground RealOpenIntervals
  SmoothCompactSet SmoothCompactImage SmoothCompactInteriorThickening
  CurrentLipschitzCompactImage CurrentHomotopyUP CurrentHomotopyGeometry
  CurrentAffineHomotopySealed CurrentAffineHomotopyClass CurrentAffineHomotopyFiniteClass
  CurrentAffineHomotopyContinuousNeighbourhood HomotopyParameterCompactBand
  MetricOpenThickening MetricOpenThickeningClosure MetricCompactNeighbourhood.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentAffineCompactSourceMargin.
Variable R:realType.
Variables n nu:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation Z:=(R_n R (1+n)%N).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation NZ:=(inner_norm (@euclidean_inner_productP R (1+n)%N)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation hNZ:=(inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N)).
Local Notation XT:=(real_norm_metric_space hNX).
Local Notation YT:=(real_norm_metric_space hNY).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variables f g:X->Y.
Hypothesis hf:norm_class_zero NX NY U f.
Hypothesis hg:norm_class_zero NX NY U g.
Variable K:smooth_compact_set hNX U.
Hypothesis hBand:forall (t:R) (x:X),0<=t<=1->smooth_compact_carrier K x->
  V ((1-t)*:f x+t*:g x).
Local Notation H:=(@CurrentAffineHomotopy.value R n nu f g).

(** Source for [current_affine_compact_source_margin]: the
    original affine image over K has a uniform open target
    margin on a compactly enlarged source and bounded open
    time interval, supporting Federer 4.1.14, pp. 371–372.
    Empty K yields empty W without selecting a target point. *)
Theorem current_affine_compact_source_margin:
  exists A:set R,exists W:set X,exists L:smooth_compact_set hNX U,
  exists d:R,
    @is_homotopy_parameter_interval R A /\
    @open XT W /\smooth_compact_carrier K `<=` W /\
    W `<=` smooth_compact_carrier L /\
    (smooth_compact_carrier K=set0->W=set0) /\0<d /\
    (forall t,A t->`|t|<=2 /\`|1-t|<=2) /\
    forall t x y,A t->W x->
      NY (y-((1-t)*:f x+t*:g x))<d->V y.
Proof.
have[A0 [W0 [hA0 [hW0 [hKW0 [hW0U hImage]]]]]]:=
  @current_affine_homotopy_continuous_neighbourhood R n nu U V hU hV
    f g hf hg K hBand.
have[r [hr hClosedTime]]:=@homotopy_parameter_compact_band R A0 hA0.
have /andP[hrPositive hrOne]:=hr.
pose A:=@real_open_interval R (-r) (1+r).
have hA:@is_homotopy_parameter_interval R A:=
  @homotopy_parameter_symmetric_enlargement R r hrPositive.
have hW0Interior:forall x,W0 x->norm_domain_interior NX W0 x.
  move=>x hx;exact:(@norm_domain_interior_neighbourhood R X NX hNX W0 x).2
    (open_nbhs_nbhs (conj hW0 hx)).
pose K0:=@current_compact_index_in_open R n U W0 K hKW0.
have[s [hs [L0 [hKL0 hL0Tube]]]]:=@smooth_compact_interior_thickening R X NX hNX
  n (@coordinate_basis R n) (@coordinate_basisP R n) W0 hW0Interior K0.
have hL0U:smooth_compact_carrier L0 `<=` U.
  move=>x hx;exact:hW0U x (smooth_compact_in_domain L0 x hx).
pose L:=@current_compact_index_in_open R n W0 U L0 hL0U.
pose W:set X:=@metric_open_thickening R XT (smooth_compact_carrier K) (s/2).
have hW:@open XT W:=@metric_open_thickening_open R XT (smooth_compact_carrier K) (s/2).
have hHalf:0<s/2 by rewrite divr_gt0 // ltr0n.
have hKW:smooth_compact_carrier K `<=` W:=
  @metric_open_thickening_includes R XT (smooth_compact_carrier K) (s/2) hHalf.
have hWL:W `<=` smooth_compact_carrier L.
  move=>x [z hz hDistance];apply:(hL0Tube x z hz).
  change (is_true (NX (z-x)<s/2)) in hDistance.
  have hSym:NX (x-z)=NX (z-x):=real_seminorm_subtract hNX.1 x z.
  rewrite hSym;have hHalfLe:s/2<=s by lra.
  exact:le_trans (ltW hDistance) hHalfLe.
pose AU:=@current_homotopy_product_domain R n A0 U.
pose C:set Z:=@euclidean_cartesian_set R 1%N n
  [set a | -r<=@euclidean_one_project R a<=1+r] (smooth_compact_carrier L).
have hC:@compact (real_norm_metric_space hNZ) C.
  exact:(@current_cartesian_compact R 1%N n
    [set a | -r<=@euclidean_one_project R a<=1+r] (smooth_compact_carrier L)
    (@scalar_current_closed_interval_compact R (-r) (1+r)) (smooth_compact_is_compact L)).
have hCAU:C `<=` AU.
  move=>z [ht hx];split.
  - exact:hClosedTime _ ht.
  - exact:smooth_compact_in_domain L _ hx.
pose CK:=@Build_smooth_compact_set R Z NZ hNZ AU C hCAU hC.
have hHClass:=@current_affine_homotopy_continuous R n nu f g A0 hA0 U hU hf hg.
pose image:=@smooth_compact_image R Z Y NZ NY hNZ hNY AU (fun _:Y=>True)
  H (fun _ _=>Logic.I) hHClass CK.
have hImageCompact:@compact YT (H @` C):=smooth_compact_is_compact image.
have hImageV:H @` C `<=` V.
  move=>y [z [ht hx] <-].
  rewrite current_affine_homotopy_coordinates.
  apply:hImage.
  - exact:hClosedTime _ ht.
  - exact:smooth_compact_in_domain L0 _ hx.
have hVOpen:@open YT V.
  rewrite openE=>y hy;exact:(@norm_domain_interior_neighbourhood R Y NY hNY V y).1
    (@hV y hy).
have[d [hd hMargin]]:=@compact_metric_open_thickening R YT (H @` C) V
  hImageCompact hVOpen hImageV.
exists A,W,L,d;split;first exact:hA.
split;first exact:hW.
split;first exact:hKW.
split;first exact:hWL.
split.
- move=>hEmpty;rewrite /W hEmpty.
  exact:(@metric_open_thickening_empty R XT (s/2)).
- split;first exact:hd.
  split.
  + move=>t [htLow htHigh].
    split;rewrite ler_norml;apply/andP;split;lra.
  + move=>t x y [htLow htHigh] hx hNear;apply:hMargin.
    pose z:=@euclidean_block_join R 1%N n (@euclidean_one_embed R t,x).
    exists (H z).
    * exists z;last by [].
      change (-r<=@euclidean_one_project R
        (@euclidean_block_split R 1%N n z).1<=1+r /\
        smooth_compact_carrier L (@euclidean_block_split R 1%N n z).2).
      rewrite /z euclidean_block_joinK euclidean_one_embedK.
      split;first by apply/andP;split;exact:ltW htLow || exact:ltW htHigh.
      exact:hWL x hx.
    * rewrite /z CurrentAffineHomotopy.laws.
      change (is_true (NY (((1-t)*:f x+t*:g x)-y)<d)).
      rewrite (real_seminorm_subtract hNY.1);exact:hNear.
Qed.
End CurrentAffineCompactSourceMargin.
