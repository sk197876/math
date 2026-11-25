(** Federer (1969), 4.1.11, p. 366: the
    original unit square is preserved by the quarter
    turn (s,t) mapped to (t,1-s). Reuse the
    preceding time-reflection and Cartesian interchange
    calculation, with its exact positive sign in degree two. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap
  CurrentSpaces CurrentCartesianDomain CurrentCartesianProductSealed CurrentCartesianCompactCurrents
  CurrentDomainTransport CurrentDegreeTransportIdentity CurrentCompactMapDomainTransport
  CurrentCompactPushforwardAlgebra CurrentCartesianMapPullback CurrentAmbientCartesianProduct
  CurrentJoinDomain CurrentJoinSourceCompact CurrentJoinReverseMapClass CurrentJoinReverseInnerCurrent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentUnitSquareRotation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation Full := (fun d:nat=>fun _:R_n R d=>True).
Local Notation hFull := (fun (d:nat) (x:R_n R d) (_:True)=>
  @norm_full_domain_interior R (R_n R d) (inner_norm (@euclidean_inner_productP R d)) x).
Local Notation Domain := (@euclidean_cartesian_set R 1%N 1%N (Full 1%N) (Full 1%N)).
Local Notation hDomain := (@current_cartesian_domain_open R 1%N 1%N
  (Full 1%N) (Full 1%N) (hFull 1%N) (hFull 1%N)).
Local Notation I := (@current_join_time_segment R h2).
Local Notation hI := (@current_join_time_segment_compact R h2).
Local Notation Raw := (@CartesianCurrentProduct.value R h2 1%N 1%N 1%N 1%N
  (Full 1%N) (Full 1%N) (hFull 1%N) (hFull 1%N) I I).
Local Notation hRaw := (@current_cartesian_compact_currents R h2 1%N 1%N 1%N 1%N
  (Full 1%N) (Full 1%N) (hFull 1%N) (hFull 1%N) I I hI hI).
Local Notation Square := (@current_ambient_cartesian_product R h2 1%N 1%N 1%N 1%N I I).
Local Notation hSquare := (@current_ambient_cartesian_product_compact R h2 1%N 1%N 1%N 1%N I I hI hI).
Local Notation Q := (@current_join_reverse_inner_map R 1%N).
Local Notation QGlobal := (@current_join_reverse_inner_smooth R 1%N).
Local Notation QOldClass := (@current_cartesian_factor_open_class R 2%N 2%N Domain hDomain Q QGlobal).
Local Notation OldImage := (fun (p:R_n R 2%N) (_:Domain p)=>conj Logic.I Logic.I).
Local Notation Image := (fun (p:R_n R 2%N) (_:True)=>Logic.I).

(** Source for [current_unit_square_rotation]: the actual
    original square current is invariant under its
    positive quarter-turn map, supporting the f square
    image in Federer 4.1.11, p. 366. This is
    the already proved inner reversal with j=1. *)
Lemma current_unit_square_rotation:
  @current_compact_map_pushforward R h2 2%N 2%N (Full 2%N) (Full 2%N)
    (hFull 2%N) (hFull 2%N) Q Image QGlobal 2%N Square hSquare=Square.
Proof.
have hOld:=@current_join_reverse_inner_current R h2 1%N 1%N I hI.
rewrite current_degree_transport_identity expr2 mulrNN mul1r scale1r in hOld.
have hDomains:=@current_compact_map_domain_transport R h2 2%N 2%N
  Domain (Full 2%N) Domain (Full 2%N) hDomain (hFull 2%N) hDomain (hFull 2%N)
  (@current_cartesian_full_domain R 1%N 1%N) (@current_cartesian_full_domain R 1%N 1%N)
  Q OldImage Image QOldClass QGlobal 2%N Raw hRaw hSquare.
by rewrite hOld in hDomains.
Qed.
End CurrentUnitSquareRotation.
