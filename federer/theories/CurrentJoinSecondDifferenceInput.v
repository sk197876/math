(** Federer (1969), 4.1.11, pp. 365–366: apply
    the original join linearity when the second compact
    current is proved equal to a difference. Reuse
    public congruence and subtraction, with no normalized
    representation or additional compactness hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  CurrentJoinSealed CurrentJoinCongruence CurrentJoinSecondDifference.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentJoinSecondDifferenceInput.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n i j:nat.
Local Notation X := (R_n R n).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X
  (inner_norm (@euclidean_inner_productP R n)) x).
Local Notation C := (fun d=>@current_space R h2 n Full hFull d).
Local Notation Compact := (fun d (T:C d)=>@compact
  (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
  (@current_support R h2 n Full hFull d T)).
Variable S:C i.
Hypothesis hS:Compact i S.

(** Source for [current_join_second_difference_input]:
    if V=T-U, then S join V=S join T-S join U,
    supporting the original prism boundary calculation
    in Federer 4.1.11, p. 366. Every compactness
    witness of the original currents is permitted. *)
Theorem current_join_second_difference_input (T U V:C j)
    (hT:Compact j T) (hU:Compact j U) (hV:Compact j V):
  V=T-U->@CurrentJoin.value R h2 n i j S V hS hV=
    @CurrentJoin.value R h2 n i j S T hS hT-
    @CurrentJoin.value R h2 n i j S U hS hU.
Proof.
move=>hEqual.
have hDifference:Compact j (T-U) by rewrite -hEqual;exact:hV.
have hInput:=@current_join_current_congruence R h2 n i j S S V (T-U)
  hS hS hV hDifference (erefl S) hEqual.
exact:(eq_trans hInput (@current_join_second_subtract R h2 n i j S hS T U hT hU hDifference)).
Qed.
End CurrentJoinSecondDifferenceInput.
