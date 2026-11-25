(** Federer (1969), 4.1.11, p. 366: the
    first positive-dimensional prism boundary. The two
    original triangular cells leave the upper and lower
    source segments and the two vertical segments.
    Reuse the original join boundary and point laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  CurrentDirac CurrentBoundary CurrentCompactBoundarySmooth CurrentCompactElementaryPushforwards
  CurrentJoinSealed CurrentJoinSecondDifferenceInput CurrentJoinPointSegment
  OrientedSimplexCurrentUP OrientedSimplexCurrentSealed OrientedSimplexCurrentLaws
  OrientedSimplexCurrentLowDegrees OrientedSimplexCurrentBoundaryRecursion OrientedSimplexFaceIndices
  CurrentSimplexPrismSum CurrentPrismFaceSum CurrentPrismBoundaryRecursion CurrentPrismPointJoin.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentPrismBoundaryLine.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n p:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R p).
Local Notation Full := (fun _:Y=>True).
Local Notation hFull := (fun (x:Y) (_:True)=>@norm_full_domain_interior R Y
  (inner_norm (@euclidean_inner_productP R p)) x).
Local Notation C := (fun d=>@current_space R h2 p Full hFull d).
Local Notation Compact := (fun d (T:C d)=>@compact
  (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R p)))
  (@current_support R h2 p Full hFull d T)).
Local Notation Boundary := (fun d=>@current_boundary R h2 p d Full hFull).
Local Notation F := (fun (d:nat) (w:'I_(d.+1)->Y)=>@OrientedSimplexCurrent.value R h2 p d w).
Local Notation D := (@dirac_current R h2 p Full hFull).
Local Notation hD := (fun x:Y=>@current_compact_dirac_support R h2 p Full hFull x Logic.I).
Variables A B:X->Y.
Local Notation PSum := (fun (d:nat) (w:'I_(d.+1)->X)=>@current_simplex_prism_sum R h2 n p A B d w).
Variable v:'I_2->X.
Local Notation a0 := (A (v ord0)).
Local Notation a1 := (A (v (lift ord0 ord0))).
Local Notation b0 := (B (v ord0)).
Local Notation b1 := (B (v (lift ord0 ord0))).
Local Notation J := (fun (T:C 0%N) (hT:Compact 0%N T)=>
  @CurrentJoin.value R h2 p 0%N 0%N (D a0) T (hD a0) hT).
Local Notation Upper := (F 1%N (fun r=>B (v r))).
Local Notation Lower := (F 1%N (fun r=>A (v r))).
Local Notation VT := (PSum 0%N (current_simplex_tail v)).
Local Notation VF := (PSum 0%N (current_simplex_face v (lift ord0 ord0))).
Local Notation hUpper := (@oriented_simplex_current_compact R h2 p 1%N (fun r=>B (v r))).
Local Notation hVT := (@current_simplex_prism_sum_compact R h2 n p A B 0%N (current_simplex_tail v)).
Local Notation hBUCompact := (@current_compact_boundary_compact R h2 p 0%N Full hFull Upper hUpper).
Local Notation hBVCompact := (@current_compact_boundary_compact R h2 p 0%N Full hFull VT hVT).

(** Source for [current_prism_boundary_line]: the boundary
    of the original signed triangular prism sum is the
    upper segment minus the lower segment minus the
    signed prisms over the source endpoints, supporting
    the induction in Federer 4.1.11, p. 366. The
    endpoint maps may identify any of the vertices. *)
Theorem current_prism_boundary_line:
  Boundary 1%N (PSum 1%N v)=Upper-Lower-@current_prism_face_sum R h2 n p A B 0%N v.
Proof.
cbn beta.
have hUpperBoundary:Boundary 0%N Upper=D b1-D b0.
  have h:=@oriented_simplex_current_boundary_segment R h2 p (fun r=>B (v r)).
  rewrite oriented_simplex_current_point in h;exact:h.
have hVerticalBoundary:Boundary 0%N VT=D b1-D a1:=
  @current_prism_sum_boundary_point R h2 n p A B (current_simplex_tail v).
have hJBU:=@current_join_second_difference_input R h2 p 0%N 0%N (D a0) (hD a0)
  (D b1) (D b0) (Boundary 0%N Upper) (hD b1) (hD b0) hBUCompact hUpperBoundary.
have hJBV:=@current_join_second_difference_input R h2 p 0%N 0%N (D a0) (hD a0)
  (D b1) (D a1) (Boundary 0%N VT) (hD b1) (hD a1) hBVCompact hVerticalBoundary.
have hHead:current_simplex_face v (lift ord0 ord0) ord0=v ord0.
  have hIndex:(lift ord0 (ord0:'I_1))=(ord_max:'I_2) by apply:val_inj;reflexivity.
  rewrite hIndex;exact:(@current_simplex_pair_last_face X v).
have hVF:=@current_prism_point_join R h2 n p A B (current_simplex_face v (lift ord0 ord0)).
rewrite hHead in hVF.
have hSegment:=@oriented_simplex_current_segment R h2 p (fun r=>A (v r))
  (fun (t:R) (_:t \in `[0,1])=>Logic.I).
have hPair:=@current_join_point_segment R h2 p a0 a1
  (fun (t:R) (_:t \in `[0,1])=>Logic.I).
have hLower:J (D a1) (hD a1)=Lower:=eq_trans hPair (esym hSegment).
cbn beta in hLower.
have hRec:=@current_prism_sum_boundary_recursion R h2 n p A B 0%N v.
cbn beta in hRec.
rewrite hJBU hJBV -hVF hLower in hRec.
have hCancel (x y z t u:C 1%N):x-y-(z-t)+(z-u)=x-u-(y-t).
  rewrite !opprB [x-y+(t-z)]addrA subrKA !addrA.
  rewrite [x-y+t]addrAC [x-u+t]addrAC.
  exact:addrAC.
rewrite hCancel in hRec.
rewrite current_prism_face_sum_pair.
exact:hRec.
Qed.
End CurrentPrismBoundaryLine.
