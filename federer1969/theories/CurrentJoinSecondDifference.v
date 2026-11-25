(** Federer (1969), 4.1.11, pp. 365–366: the
    original join preserves differences in its second
    compact factor. This is the preceding linearity,
    with every compactness witness allowed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  CurrentJoinSealed CurrentJoinLinearity CurrentJoinCongruence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentJoinSecondDifference.
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

(** Source for [current_join_second_subtract]: S join
    (T-U)=S join T-S join U on the original compact
    currents, supporting the prism boundary calculation in
    Federer 4.1.11, p. 366. *)
Theorem current_join_second_subtract (T U:C j) (hT:Compact j T) (hU:Compact j U)
    (hDifference:Compact j (T-U)):
  @CurrentJoin.value R h2 n i j S (T-U) hS hDifference=
    @CurrentJoin.value R h2 n i j S T hS hT-
    @CurrentJoin.value R h2 n i j S U hS hU.
Proof.
have hCombination:Compact j ((-1:R)*:U+T) by rewrite scaleN1r addrC.
have hLinear:=@current_join_second_linear R h2 n i j (-1:R) S U T hS hU hT hCombination.
have hInput:=@current_join_current_congruence R h2 n i j S S ((-1:R)*:U+T) (T-U)
  hS hS hCombination hDifference (erefl S) (ltac:(by rewrite scaleN1r addrC)).
rewrite hInput scaleN1r in hLinear.
exact:(eq_trans hLinear (addrC
  (-@CurrentJoin.value R h2 n i j S U hS hU) (@CurrentJoin.value R h2 n i j S T hS hT))).
Qed.
End CurrentJoinSecondDifference.
