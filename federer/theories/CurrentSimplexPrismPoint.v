(** Federer (1969), 4.1.11, p. 366: the
    zero-dimensional case of the original prism formula.
    The original segment times a point is its affine
    inclusion image, hence the ordered endpoint simplex.
    Keep coincident endpoints and zero-dimensional factors. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanBlockCoordinates Biorthogonal
  CurrentSpaces CurrentDirac CurrentDegreeTransportIdentity CurrentCartesianPointInclusion
  CurrentSegmentMapUP OrientedSegmentCurrentSealed CurrentAmbientCartesianProduct
  CurrentAmbientRightPointProduct OrientedSimplexCurrentSealed OrientedSimplexCurrentLaws
  OrientedSimplexCurrentLowDegrees CurrentSimplexPrismSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentSimplexPrismPoint.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables p n:nat.
Local Notation Full := (fun d:nat=>fun _:R_n R d=>True).
Local Notation hFull := (fun (d:nat) (x:R_n R d) (_:True)=>
  @norm_full_domain_interior R (R_n R d) (inner_norm (@euclidean_inner_productP R d)) x).
Variables a b:R_n R p.
Local Notation Lower := (@current_cartesian_point_inclusion R p n a).
Local Notation Upper := (@current_cartesian_point_inclusion R p n b).
Local Notation Segment := (@OrientedSegmentCurrent.value R h2 p (Full p) (hFull p)
  a b (fun (t:R) (_:t \in `[0,1])=>Logic.I)).

(** Source for [current_simplex_prism_point]: the
    original [a,b] times [u] is [(a,u),(b,u)],
    the m=0 endpoint of the printed prism sum in
    Federer 4.1.11, p. 366. This includes a=b
    and every pair of Euclidean factor dimensions. *)
Theorem current_simplex_prism_point (v:'I_1->R_n R n):
  @current_ambient_cartesian_product R h2 p n 1%N 0%N Segment
    (@OrientedSimplexCurrent.value R h2 n 0%N v)=
  @current_simplex_prism_sum R h2 n (p+n)%N Lower Upper 0%N v.
Proof.
rewrite oriented_simplex_current_point.
pose w:=ordinal_cons a (fun _:'I_1=>b).
have hRight:=@current_ambient_right_point_simplex R h2 p n (v ord0) 1%N w.
rewrite current_degree_transport_identity in hRight.
have hSegment:=@oriented_simplex_current_segment R h2 p w
  (fun (t:R) (_:t \in `[0,1])=>Logic.I).
rewrite /w ordinal_cons0 ordinal_consS in hSegment.
rewrite hSegment in hRight.
have hVertices:(fun k=>@euclidean_block_join R p n (w k,v ord0))=
    ordinal_cons (Lower (v ord0)) (fun r:'I_1=>Upper (v r)).
  apply:funext=>k;case:(unliftP ord0 k)=>[r ->|->].
  + rewrite /w !ordinal_consS.
    have hr:r=ord0:=ord1 r.
    by rewrite hr.
  + by rewrite /w !ordinal_cons0.
rewrite (@current_simplex_prism_sum_point R h2 n (p+n)%N Lower Upper v).
exact:(eq_trans hRight (congr1 (@OrientedSimplexCurrent.value R h2 (p+n)%N 1%N) hVertices)).
Qed.
End CurrentSimplexPrismPoint.
