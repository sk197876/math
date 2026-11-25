(** Federer (1969), 4.1.14, p. 371: a continuous affine
    deformation whose segments over K lie in V maps a whole
    smaller open time-space neighbourhood into V. This uses
    the compact-product argument of 4.1.13, pp. 369–370,
    with continuity in place of smoothness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology num_normedtype normed_module.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormClassOneUP
  NormRegularity NormBoundedLinearTopology NormOpenPreimage
  InnerNorm InnerMetric HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanBlockNormTopology
  EuclideanDistributionMeasureContext TopologicalProductMaps
  RealMetricBackground SmoothCompactSet CurrentHomotopyUP CurrentHomotopyGeometry
  CurrentHomotopyDomain CurrentAffineHomotopyUP CurrentAffineHomotopySealed
  CurrentAffineHomotopyClass CurrentAffineHomotopyFiniteClass
  CompactProductOpenNeighbourhood HomotopyParameterNeighbourhood.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentAffineHomotopyContinuousNeighbourhood.
Variable R:realType.
Variables n nu:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation Z := (R_n R (1+n)%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R (1+n)%N)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N)).
Local Notation hNT := (inner_norm_real_norm (@euclidean_inner_productP R 1%N)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation TT := (real_norm_metric_space hNT).
Local Notation ZT := (real_norm_metric_space hNZ).
Local Notation RT := (real_line_metric R).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variables f g:X->Y.
Hypothesis hf:norm_class_zero NX NY U f.
Hypothesis hg:norm_class_zero NX NY U g.
Variable K:smooth_compact_set hNX U.
Hypothesis hBand:forall (t:R) (x:X),0<=t<=1->smooth_compact_carrier K x->
  V ((1-t)*:f x+t*:g x).
Local Notation H := (@CurrentAffineHomotopy.value R n nu f g).
Local Notation Full := (fun _:R=>True).
Local Notation FullU := (@current_homotopy_product_domain R n Full U).

(** Source for [current_affine_homotopy_continuous_neighbourhood]:
    shrink the source around the support before applying the
    locally Lipschitz affine formula of Federer 4.1.14, p. 371.
    Only the original support-segment condition is required;
    the target need not be convex and K may be empty. *)
Theorem current_affine_homotopy_continuous_neighbourhood:
  exists (A:set R) (W:set X),
    @is_homotopy_parameter_interval R A /\@open XT W /\
    smooth_compact_carrier K `<=` W /\W `<=` U /\
    forall t x,A t->W x->V ((1-t)*:f x+t*:g x).
Proof.
have hFull:@is_homotopy_parameter_interval R Full.
  constructor;first exact:openT;by [].
have hContinuous:=@current_affine_homotopy_continuous R n nu f g
  Full hFull U hU hf hg.
have hVOpen:@open (real_norm_metric_space hNY) V.
  rewrite openE=>y hy.
  exact:((@norm_domain_interior_neighbourhood R Y NY hNY V y).1 (@hV y hy)).
pose O:set Z:=[set z|FullU z /\V (H z)].
have hO:@open ZT O.
  exact:(@norm_class_zero_open_preimage R Z Y NZ NY hNZ hNY
    FullU V H hContinuous hVOpen).
have hEmbed:continuous (fun t:RT=>(@euclidean_one_embed R t:TT)).
  move=>t.
  exact (@continuous_comp
    [the topologicalType of RT]
    [the topologicalType of inner_metric_space (@euclidean_inner_productP R 1%N)]
    [the topologicalType of TT]
    (@euclidean_one_embed R)
    (fun z:inner_metric_space (@euclidean_inner_productP R 1%N)=>(z:TT))
    t (@euclidean_one_embed_continuous R t)
    (@euclidean_distribution_inner_to_norm R 1%N (@euclidean_one_embed R t))).
pose J (p:XT*RT):ZT:=@euclidean_block_join R 1%N n
  (@euclidean_one_embed R p.2,p.1).
have hTime:continuous (fun p:XT*RT=>(@euclidean_one_embed R p.2:TT)).
  move=>p;exact:(continuous_comp (@second_projection_continuous XT RT p) (@hEmbed p.2)).
have hPair:continuous (fun p:XT*RT=>(@euclidean_one_embed R p.2,p.1):(TT*XT)%type).
  exact:topological_pair_continuous hTime (@first_projection_continuous XT RT).
have hJ:continuous J.
  move=>p;exact:(continuous_comp (@hPair p)
    (@euclidean_block_join_norm_continuous R 1%N n (@euclidean_one_embed R p.2,p.1))).
have hPre:@open [the topologicalType of (XT*RT)%type] (J @^-1` O).
  exact:((@continuousP [the topologicalType of (XT*RT)%type] ZT J).1 hJ O hO).
have hI:@compact RT (`[0,1]:set RT).
  exact:segment_compact.
have hInside:(smooth_compact_carrier K:set XT) `*` (`[0,1]:set RT) `<=` (J @^-1` O).
  move=>[x t] [hx ht];split.
  - exact:(@current_homotopy_join_member R n Full U t x Logic.I
      (smooth_compact_in_domain K x hx)).
  - rewrite /J CurrentAffineHomotopy.laws.
    apply:hBand=>//;by move:ht;rewrite /mkset in_itv /=.
have [W [B [hW [hB [hKW [hIB hWB]]]]]]:=
  @compact_product_open_neighbourhood XT RT
    (smooth_compact_carrier K) (`[0,1]) (J @^-1` O)
    (smooth_compact_is_compact K) hI hPre hInside.
have [A [hA hAB]]:=@homotopy_parameter_neighbourhood R B hB hIB.
have hWU:W `<=` U.
  move=>x hx.
  have hZero:(`[0,1]:set RT) 0 by rewrite /mkset in_itv /= lexx ler01.
  have hz:O (J (x,0)):=hWB (x,0) (conj hx (hIB 0 hZero)).
  have hDomain:=hz.1.
  change (Full (@euclidean_one_project R
    (@euclidean_block_split R 1%N n (J (x,0))).1) /\
    U (@euclidean_block_split R 1%N n (J (x,0))).2) in hDomain.
  move:hDomain;rewrite /J euclidean_block_joinK;by move=>[_].
exists A,W;split;first exact:hA.
split;first exact:hW.
split;first exact:hKW.
split;first exact:hWU.
move=>t x ht hx.
have hz:O (J (x,t)):=hWB (x,t) (conj hx (hAB t ht)).
by move:hz.2;rewrite /J CurrentAffineHomotopy.laws.
Qed.
End CurrentAffineHomotopyContinuousNeighbourhood.
