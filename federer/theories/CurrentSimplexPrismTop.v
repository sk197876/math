(** Federer (1969), 4.1.11, p. 366: identify
    the Cartesian prism and its signed simplex sum
    in positive top degree from their common boundary.
    Reuse compact support and the preceding compact
    top-degree uniqueness consequence of 4.1.10, p. 364. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  CurrentBoundary CurrentSupportGeometry CurrentSegmentMapUP CurrentSegmentCompactSet
  OrientedSegmentCurrentSealed OrientedSegmentCurrentSupport CurrentCartesianPointInclusion
  CurrentAmbientCartesianProduct CurrentCompactTopUniqueness OrientedSimplexCurrentSealed
  OrientedSimplexCurrentLaws CurrentSimplexPrismSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentSimplexPrismTop.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables p n m:nat.
Local Notation Full := (fun d:nat=>fun _:R_n R d=>True).
Local Notation hFull := (fun (d:nat) (x:R_n R d) (_:True)=>
  @norm_full_domain_interior R (R_n R d) (inner_norm (@euclidean_inner_productP R d)) x).
Variables a b:R_n R p.
Local Notation Lower := (@current_cartesian_point_inclusion R p n a).
Local Notation Upper := (@current_cartesian_point_inclusion R p n b).
Local Notation hSegment := (fun (t:R) (_:t \in `[0,1])=>Logic.I).
Local Notation Segment := (@OrientedSegmentCurrent.value R h2 p (Full p) (hFull p) a b hSegment).
Variable v:'I_(m.+1)->R_n R n.
Local Notation S := (@current_ambient_cartesian_product R h2 p n 1%N m Segment
  (@OrientedSimplexCurrent.value R h2 n m v)).
Local Notation T := (@current_simplex_prism_sum R h2 n (p+n)%N Lower Upper m v).

(** Source for [current_simplex_prism_top]: in the
    original positive top degree, equality of boundaries
    gives equality of the Cartesian prism and signed
    simplex sum, Federer 4.1.11, p. 366. The
    final arbitrary-ambient theorem removes this reduction
    by the original affine parametrisation argument. *)
Theorem current_simplex_prism_top:
  (p+n)%N=m.+1->
  @current_boundary R h2 (p+n)%N m (Full (p+n)%N) (hFull (p+n)%N) S=
    @current_boundary R h2 (p+n)%N m (Full (p+n)%N) (hFull (p+n)%N) T->S=T.
Proof.
move=>hDegree hBoundary.
pose K:=@current_segment_compact_set R p (Full p) a b hSegment.
have hCompactSegment:@compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R p)))
    (@current_support R h2 p (Full p) (hFull p) 1%N Segment).
  exact:(@current_support_compact_bound R h2 p 1%N (Full p) (hFull p) K Segment
    (@oriented_segment_current_support R h2 p (Full p) (hFull p) a b hSegment)).
have hCompactSimplex:=@oriented_simplex_current_compact R h2 n m v.
have hS:=@current_ambient_cartesian_product_compact R h2 p n 1%N m Segment
  (@OrientedSimplexCurrent.value R h2 n m v) hCompactSegment hCompactSimplex.
have hT:=@current_simplex_prism_sum_compact R h2 n (p+n)%N Lower Upper m v.
exact:(@current_compact_top_boundary_unique R h2 (p+n)%N m (Full (p+n)%N) (hFull (p+n)%N)
  S T hS hT hDegree hBoundary).
Qed.
End CurrentSimplexPrismTop.
