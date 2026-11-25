(** Federer (1969), 4.1.11, p. 366: the
    original signed prisms over the ordered faces of
    the source simplex. Keep the literal finite face
    sum needed for the original boundary induction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  CurrentCompactFiniteSum OrientedSimplexCurrentUP CurrentSimplexPrismSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentPrismFaceSum.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n p:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R p).
Local Notation Full := (fun _:Y=>True).
Local Notation hFull := (fun (x:Y) (_:True)=>@norm_full_domain_interior R Y
  (inner_norm (@euclidean_inner_productP R p)) x).
Local Notation C := (fun m=>@current_space R h2 p Full hFull m).
Variables A B:X->Y.
Local Notation PSum := (fun (m:nat) (v:'I_(m.+1)->X)=>
  @current_simplex_prism_sum R h2 n p A B m v).

(** Source for [current_prism_face_sum]: the original
    alternating sum of the prisms over all source
    faces, supporting the boundary proof in Federer
    4.1.11, p. 366. This finite expression introduces
    no new boundary operator or negative degree. *)
Definition current_prism_face_sum m (v:'I_(m.+2)->X):C m.+1:=
  \sum_(k<m.+2) (-1:R)^+k*:PSum m (current_simplex_face v k).

(** Source for [current_prism_face_sum_compact]: the
    original signed source-face prism sum has compact
    support, supporting Federer 4.1.11, p. 366. *)
Theorem current_prism_face_sum_compact m (v:'I_(m.+2)->X):
  @compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R p)))
    (@current_support R h2 p Full hFull m.+1 (current_prism_face_sum v)).
Proof.
exact:(@current_compact_weighted_finite_sum R h2 p m.+1 Full hFull m.+2
  (fun k=>(-1:R)^+k) (fun k=>PSum m (current_simplex_face v k))
  (fun k=>@current_simplex_prism_sum_compact R h2 n p A B m (current_simplex_face v k))).
Qed.

(** Source for [current_prism_face_sum_pair]: for a
    source segment the original face prism sum is
    its last vertical segment minus its first vertical
    segment, supporting Federer 4.1.11, p. 366. *)
Theorem current_prism_face_sum_pair (v:'I_2->X):
  current_prism_face_sum v=PSum 0%N (current_simplex_tail v)-
    PSum 0%N (current_simplex_face v (lift ord0 ord0)).
Proof.
by rewrite /current_prism_face_sum big_ord_recl big_ord1 lift0 expr0 expr1 scale1r scaleN1r.
Qed.
End CurrentPrismFaceSum.
