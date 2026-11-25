(** Federer (1969), 4.1.11, p. 366: the literal
    finite signed sum of the original prism simplexes.
    Its compactness and point-join recursion are derived
    from the public vertex and simplex laws. No prism
    current equality or associativity is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct Biorthogonal
  CurrentSpaces CurrentDirac CurrentCompactElementaryPushforwards CurrentCompactFiniteSum
  CurrentJoinSealed CurrentJoinFiniteLinearity OrientedSimplexCurrentUP
  OrientedSimplexCurrentSealed OrientedSimplexCurrentLaws OrientedSimplexPrepend
  CurrentPrismVerticesUP CurrentPrismVerticesSealed CurrentPrismVertexRecursion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentSimplexPrismSum.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n p:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R p).
Local Notation Full := (fun _:Y=>True).
Local Notation hFull := (fun (x:Y) (_:True)=>@norm_full_domain_interior R Y
  (inner_norm (@euclidean_inner_productP R p)) x).
Local Notation F := (fun (m:nat) (v:'I_(m.+1)->Y)=>@OrientedSimplexCurrent.value R h2 p m v).
Local Notation C := (fun m=>@current_space R h2 p Full hFull m).
Local Notation Compact := (fun m (T:C m)=>@compact
  (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R p)))
  (@current_support R h2 p Full hFull m T)).
Variables A B:X->Y.
Local Notation P := (fun (m:nat) (v:'I_(m.+1)->X) k=>@CurrentPrismVertices.value X Y A B m v k).
Local Notation hP := (@CurrentPrismVertices.laws X Y A B).

(** Source for [current_simplex_prism_sum]: the original
    sum over k=0,...,m of (-1)^k times the kth
    ordered prism simplex, Federer 4.1.11, p. 366.
    Endpoint maps remain arbitrary in this finite expression. *)
Definition current_simplex_prism_sum m (v:'I_(m.+1)->X):C m.+1:=
  \sum_(k<m.+1) (-1:R)^+k*:F m.+1 (P m v k).

(** Source for [current_simplex_prism_sum_compact]: the
    original finite prism sum has compact support,
    supporting the top-degree uniqueness argument of
    Federer 4.1.11, p. 366. *)
Theorem current_simplex_prism_sum_compact m (v:'I_(m.+1)->X):
  Compact m.+1 (current_simplex_prism_sum v).
Proof.
exact:(@current_compact_weighted_finite_sum R h2 p m.+1 Full hFull m.+1
  (fun k=>(-1:R)^+k) (fun k=>F m.+1 (P m v k))
  (fun k=>@oriented_simplex_current_compact R h2 p m.+1 (P m v k))).
Qed.

(** Source for [current_simplex_prism_sum_point]: the
    prism of a zero simplex has its original two
    endpoint vertices, supporting Federer 4.1.11, p. 366. *)
Theorem current_simplex_prism_sum_point (v:'I_1->X):
  current_simplex_prism_sum v=F 1%N (ordinal_cons (A (v ord0)) (fun r=>B (v r))).
Proof.
rewrite /current_simplex_prism_sum big_ord1 expr0 scale1r.
by rewrite (@current_prism_vertices_first X Y A B _ hP 0%N v).
Qed.

(** Source for [current_simplex_prism_sum_recursion]: the
    original signed prism sum is the first point joined
    with its upper simplex, minus the first point joined
    with the tail prism sum. This supporting regrouping
    follows the induction in Federer 4.1.11, p. 366. *)
Theorem current_simplex_prism_sum_recursion m (v:'I_(m.+2)->X):
  current_simplex_prism_sum v=
    @CurrentJoin.value R h2 p 0%N m.+1
      (@dirac_current R h2 p Full hFull (A (v ord0)))
      (F m.+1 (fun r=>B (v r)))
      (@current_compact_dirac_support R h2 p Full hFull (A (v ord0)) Logic.I)
      (@oriented_simplex_current_compact R h2 p m.+1 (fun r=>B (v r)))-
    @CurrentJoin.value R h2 p 0%N m.+1
      (@dirac_current R h2 p Full hFull (A (v ord0)))
      (current_simplex_prism_sum (current_simplex_tail v))
      (@current_compact_dirac_support R h2 p Full hFull (A (v ord0)) Logic.I)
      (@current_simplex_prism_sum_compact m (current_simplex_tail v)).
Proof.
pose Point:=@dirac_current R h2 p Full hFull (A (v ord0)).
pose hPoint:=@current_compact_dirac_support R h2 p Full hFull (A (v ord0)) Logic.I.
pose Tail:=current_simplex_tail v.
pose T:=fun k:'I_(m.+1)=>F m.+1 (P m Tail k).
pose hT:=fun k:'I_(m.+1)=>@oriented_simplex_current_compact R h2 p m.+1 (P m Tail k).
pose hSum:=@current_simplex_prism_sum_compact m Tail.
have hFinite:=@current_join_second_weighted_sum R h2 p 0%N m.+1 Point hPoint m.+1
  (fun k=>(-1:R)^+k) T hT hSum.
have hExpansion:current_simplex_prism_sum v=
    @CurrentJoin.value R h2 p 0%N m.+1 Point (F m.+1 (fun r=>B (v r))) hPoint
      (@oriented_simplex_current_compact R h2 p m.+1 (fun r=>B (v r)))-
    \sum_(k<m.+1) (-1:R)^+k*:@CurrentJoin.value R h2 p 0%N m.+1 Point (T k) hPoint (hT k).
  rewrite /current_simplex_prism_sum big_ord_recl expr0 scale1r.
  rewrite (@current_prism_vertices_first X Y A B _ hP m.+1 v) oriented_simplex_current_prepend.
  congr (_+_);rewrite -sumrN;apply:eq_bigr=>k _.
  rewrite (@current_prism_vertices_successor X Y A B _ hP m v k)
    oriented_simplex_current_prepend lift0 exprS mulN1r scaleNr.
  reflexivity.
by rewrite -hFinite in hExpansion.
Qed.
End CurrentSimplexPrismSum.
