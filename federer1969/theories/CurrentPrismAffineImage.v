(** Federer (1969), 4.1.11, p. 366: affine
    transport of the original signed prism simplex sum.
    Reuse finite compact pushforward linearity, the
    original simplex affine law and the independent
    ordered vertex ranges. Prescribed target vertices
    may be degenerate or coincide. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom AffineMaps RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanAffineSmooth
  CurrentSpaces CurrentCompactPushforwardAlgebra CurrentCompactMapFiniteSum CurrentCartesianMapPullback
  CurrentJoinAffineSourcePushforward OrientedSimplexCurrentSealed OrientedSimplexCurrentLaws
  OrientedSimplexCurrentAffine CurrentPrismVerticesSealed CurrentPrismVertexNaturality CurrentSimplexPrismSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentPrismAffineImage.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n p n' q:nat.
Local Notation Full := (fun d:nat=>fun _:R_n R d=>True).
Local Notation hFull := (fun (d:nat) (x:R_n R d) (_:True)=>
  @norm_full_domain_interior R (R_n R d) (inner_norm (@euclidean_inner_productP R d)) x).
Variables A B:R_n R n->R_n R p.
Variables A' B':R_n R n'->R_n R q.
Variable L:R_n R p->R_n R q.
Hypothesis hL:is_affine_map L.
Local Notation Image := (fun (x:R_n R p) (_:True)=>Logic.I).
Local Notation LGlobal := (@euclidean_affine_map_smooth R p q (Full p) (hFull p) L hL).
Local Notation LClass := (@current_cartesian_factor_open_class R p q (Full p) (hFull p) L LGlobal).
Variable m:nat.
Variable v:'I_(m.+1)->R_n R n.
Variable w:'I_(m.+1)->R_n R n'.
Hypothesis hLower:forall r,L (A (v r))=A' (w r).
Hypothesis hUpper:forall r,L (B (v r))=B' (w r).
Local Notation Source := (@current_simplex_prism_sum R h2 n p A B m v).
Local Notation hSource := (@current_simplex_prism_sum_compact R h2 n p A B m v).

(** Source for [current_prism_affine_image]: the original
    affine image of the source prism sum is the
    prism sum with the prescribed target endpoint
    vertices, supporting the arbitrary-ambient transfer
    in Federer 4.1.11, p. 366. Every target
    vertex family and all zero endpoints are retained. *)
Theorem current_prism_affine_image:
  @current_join_affine_current R h2 p q L hL m.+1 Source hSource=
  @current_simplex_prism_sum R h2 n' q A' B' m w.
Proof.
pose P:=fun k:'I_(m.+1)=>@CurrentPrismVertices.value (R_n R n) (R_n R p) A B m v k.
pose T:=fun k:'I_(m.+1)=>@OrientedSimplexCurrent.value R h2 p m.+1 (P k).
pose hT:=fun k:'I_(m.+1)=>@oriented_simplex_current_compact R h2 p m.+1 (P k).
have hFinite:=@current_compact_map_weighted_sum R h2 p q (Full p) (Full q)
  (hFull p) (hFull q) L Image LClass m.+1 m.+1 (fun k=>(-1:R)^+k) T hT hSource.
rewrite /current_join_affine_current /current_simplex_prism_sum hFinite.
apply:eq_bigr=>k _.
have hSimplex:=@oriented_simplex_current_affine R h2 p q L hL m.+1 (P k) (hT k).
have hVertices:=@current_prism_vertices_image (R_n R n) (R_n R p) (R_n R n') (R_n R q)
  A B A' B' L m v w k hLower hUpper.
rewrite /P in hSimplex.
rewrite hVertices in hSimplex.
exact:(congr1 (fun S=>(-1:R)^+k*:S) hSimplex).
Qed.
End CurrentPrismAffineImage.
