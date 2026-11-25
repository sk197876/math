(** Federer (1969), 4.1.11, pp. 365–366: regroup
    the full original simplex boundary into its first
    face and the signed sum of its remaining faces.
    Reuse the proved all-face formula; this is the
    form used in the simplicial prism induction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentBoundary
  OrientedSimplexCurrentUP OrientedSimplexCurrentSealed OrientedSimplexCurrentBoundary.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section OrientedSimplexNonfirstBoundary.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X
  (inner_norm (@euclidean_inner_productP R n)) x).
Local Notation F := (fun (m:nat) (v:'I_(m.+1)->X)=>@OrientedSimplexCurrent.value R h2 n m v).

(** Source for [oriented_simplex_nonfirst_boundary_sum]:
    the signed sum over the nonfirst original faces
    equals the first face minus the boundary, supporting
    Federer 4.1.11, pp. 365–366. The original
    degree-one endpoint is retained. *)
Theorem oriented_simplex_nonfirst_boundary_sum m (v:'I_(m.+2)->X):
  \sum_(k<m.+1) (-1:R)^+k*:F m (current_simplex_face v (lift ord0 k))=
    F m (current_simplex_tail v)-@current_boundary R h2 n m Full hFull (F m.+1 v).
Proof.
cbn beta.
have hBoundary:=@oriented_simplex_current_boundary R h2 n m v.
rewrite big_ord_recl expr0 scale1r in hBoundary.
have hSigns:(\sum_(k<m.+1) (-1:R)^+(lift ord0 k:nat)*:
    F m (current_simplex_face v (lift ord0 k)))=
    -(\sum_(k<m.+1) (-1:R)^+k*:F m (current_simplex_face v (lift ord0 k))).
  rewrite -sumrN;apply:eq_bigr=>k _.
  by rewrite lift0 exprS mulN1r scaleNr.
cbn beta in hSigns.
rewrite hSigns in hBoundary.
by rewrite hBoundary subKr.
Qed.
End OrientedSimplexNonfirstBoundary.
