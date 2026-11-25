(** Federer (1969), 4.1.11, pp. 365–366: the
    original zero-simplex prism sum is the join of
    its two point endpoints. Reuse the original simplex
    base and prepend laws, with join congruence for
    the compactness witnesses. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct Biorthogonal
  CurrentSpaces CurrentDirac CurrentCompactElementaryPushforwards CurrentJoinSealed CurrentJoinCongruence
  OrientedSimplexCurrentSealed OrientedSimplexCurrentLaws OrientedSimplexPrepend CurrentSimplexPrismSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentPrismPointJoin.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n p:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R p).
Local Notation Full := (fun _:Y=>True).
Local Notation hFull := (fun (x:Y) (_:True)=>@norm_full_domain_interior R Y
  (inner_norm (@euclidean_inner_productP R p)) x).
Variables A B:X->Y.

(** Source for [current_prism_point_join]: the original
    prism sum over [u] is delta_(A(u)) join delta_(B(u)),
    supporting the first positive-dimensional boundary
    cancellation in Federer 4.1.11, p. 366. *)
Theorem current_prism_point_join (v:'I_1->X):
  @current_simplex_prism_sum R h2 n p A B 0%N v=
  @CurrentJoin.value R h2 p 0%N 0%N
    (@dirac_current R h2 p Full hFull (A (v ord0)))
    (@dirac_current R h2 p Full hFull (B (v ord0)))
    (@current_compact_dirac_support R h2 p Full hFull (A (v ord0)) Logic.I)
    (@current_compact_dirac_support R h2 p Full hFull (B (v ord0)) Logic.I).
Proof.
pose w:=fun r:'I_1=>B (v r).
pose P:=@dirac_current R h2 p Full hFull (A (v ord0)).
pose Q:=@dirac_current R h2 p Full hFull (B (v ord0)).
pose hP:=@current_compact_dirac_support R h2 p Full hFull (A (v ord0)) Logic.I.
pose hQ:=@current_compact_dirac_support R h2 p Full hFull (B (v ord0)) Logic.I.
pose T:=@OrientedSimplexCurrent.value R h2 p 0%N w.
pose hT:=@oriented_simplex_current_compact R h2 p 0%N w.
have hPoint:T=Q:=@oriented_simplex_current_point R h2 p w.
have hJoin:=@current_join_current_congruence R h2 p 0%N 0%N P P T Q
  hP hP hT hQ (erefl P) hPoint.
rewrite current_simplex_prism_sum_point.
exact:(eq_trans (@oriented_simplex_current_prepend R h2 p 0%N (A (v ord0)) w) hJoin).
Qed.
End CurrentPrismPointJoin.
