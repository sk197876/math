(** Federer (1969), 4.1.11, pp. 364–366: the original join
    respects the linear operations used in its boundary and simplex
    identities. Reuse the proved source-product and proper-pushforward
    linearity. Compactness of linear combinations is already proved. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  CurrentDensityUP CurrentCompactSmoothAlgebra CurrentProperSupport
  CurrentPushforwardSealed CurrentPushforwardLinear
  CurrentPushforwardCongruence CurrentJoinMapSealed CurrentJoinMapClass
  CurrentJoinDomain CurrentJoinSourceChain CurrentJoinSourceCompact
  CurrentJoinSourceLinear CurrentJoinSealed CurrentJoinLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section CurrentJoinLinearity.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n i j : nat.
Local Notation X := (R_n R n).
Local Notation Full := (fun _ : X => True).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX :=
  (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hFull := (fun (x : X) (_ : True) =>
  @norm_full_domain_interior R X NX x).
Local Notation C := (fun k => @current_space R h2 n Full hFull k).
Local Notation Compact := (fun k (T : C k) =>
  @compact (real_norm_metric_space hNX)
    (@current_support R h2 n Full hFull k T)).
Local Notation Domain := (@current_join_domain R n).
Local Notation hDomain := (@current_join_domain_open R n).
Local Notation Chain := (@current_join_source_chain R h2 n i j).
Local Notation F := (@CurrentJoinMap.value R n).
Local Notation Image := (@current_join_map_image R n).
Local Notation Smooth :=
  (@current_join_map_smooth R n Domain hDomain).
Local Notation Proper := (fun P =>
  @is_current_proper_on_support R h2 (n+(1+n))%N n (i+1+j)%N
    Domain hDomain Full P F Image).
Local Notation Join := (fun (S : C i) (T : C j) =>
  @CurrentJoin.value R h2 n i j S T).

(** Source for [current_join_first_linear]: the original join
    is linear in S, supporting the boundary and alternating simplex
    computations in Federer 4.1.11, pp. 365–366. The already proved
    compact linear-support law supplies hCombination; any such proof
    is permitted. No representation or mass hypothesis is added. *)
Theorem current_join_first_linear c (S U : C i) (T : C j)
    (hS : Compact i S) (hU : Compact i U) (hT : Compact j T)
    (hCombination : Compact i (c*:S+U)) :
  Join (c*:S+U) T hCombination hT =
    c*:Join S T hS hT + Join U T hU hT.
Proof.
have hChain := @current_join_source_first_linear R h2 n i j c S U T.
pose hpS := @current_join_source_proper R h2 n i j S T hS hT.
pose hpU := @current_join_source_proper R h2 n i j U T hU hT.
pose hpCombination := @current_join_source_proper R h2 n i j
  (c*:S+U) T hCombination hT.
have hp : Proper (c*:Chain S T+Chain U T).
  by rewrite -hChain; exact: hpCombination.
rewrite !current_join_pushforward.
apply: (eq_trans (@current_pushforward_current_congruence R h2
  (n+(1+n))%N n (i+1+j)%N Domain Full hDomain hFull
  F Image Smooth (Chain (c*:S+U) T) (c*:Chain S T+Chain U T)
  hpCombination hp hChain)).
exact: (@current_pushforward_linear R h2 (n+(1+n))%N n (i+1+j)%N
  Domain Full hDomain hFull F Image Smooth c
  (Chain S T) (Chain U T) hpS hpU hp).
Qed.

(** Source for [current_join_second_linear]: the original
    join is linear in T, supporting Federer 4.1.11, pp. 365–366.
    Compactness of cT+U follows from the earlier compact linear-
    support theorem; the result permits every such proof. *)
Theorem current_join_second_linear c (S : C i) (T U : C j)
    (hS : Compact i S) (hT : Compact j T) (hU : Compact j U)
    (hCombination : Compact j (c*:T+U)) :
  Join S (c*:T+U) hS hCombination =
    c*:Join S T hS hT + Join S U hS hU.
Proof.
have hChain := @current_join_source_second_linear R h2 n i j c S T U.
pose hpT := @current_join_source_proper R h2 n i j S T hS hT.
pose hpU := @current_join_source_proper R h2 n i j S U hS hU.
pose hpCombination := @current_join_source_proper R h2 n i j
  S (c*:T+U) hS hCombination.
have hp : Proper (c*:Chain S T+Chain S U).
  by rewrite -hChain; exact: hpCombination.
rewrite !current_join_pushforward.
apply: (eq_trans (@current_pushforward_current_congruence R h2
  (n+(1+n))%N n (i+1+j)%N Domain Full hDomain hFull
  F Image Smooth (Chain S (c*:T+U)) (c*:Chain S T+Chain S U)
  hpCombination hp hChain)).
exact: (@current_pushforward_linear R h2 (n+(1+n))%N n (i+1+j)%N
  Domain Full hDomain hFull F Image Smooth c
  (Chain S T) (Chain S U) hpT hpU hp).
Qed.
End CurrentJoinLinearity.
