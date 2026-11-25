(** Federer (1969), 4.1.11, p. 364: the original join
    exists uniquely for arbitrary compactly supported currents.
    The already proved Cartesian product and proper pushforward
    supply a witness for the independent all-test action law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  CurrentPushforwardUP CurrentPushforwardExistence CurrentJoinMapSealed
  CurrentJoinMapClass CurrentJoinDomain CurrentJoinSourceChain
  CurrentJoinSourceCompact CurrentJoinUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section CurrentJoinExistence.
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
Local Notation Domain := (@current_join_domain R n).
Local Notation hDomain := (@current_join_domain_open R n).
Variable S : @current_space R h2 n Full hFull i.
Variable T : @current_space R h2 n Full hFull j.
Hypothesis hS : @compact (real_norm_metric_space hNX)
  (@current_support R h2 n Full hFull i S).
Hypothesis hT : @compact (real_norm_metric_space hNX)
  (@current_support R h2 n Full hFull j T).
Local Notation Chain := (@current_join_source_chain R h2 n i j S T).
Local Notation F := (@CurrentJoinMap.value R n).
Local Notation Image := (@current_join_map_image R n).
Local Notation Smooth :=
  (@current_join_map_smooth R n Domain hDomain).
Local Notation Proper :=
  (@current_join_source_proper R h2 n i j S T hS hT).
Local Notation C := (@current_space R h2 n Full hFull (i+1+j)%N).

(** Source for [current_join_exists]: the original join is an
    actual current of degree i+1+j under the printed compact
    support hypotheses, Federer 4.1.11, p. 364. Neither factor
    is assumed normal or representable by integration. *)
Theorem current_join_exists : exists J : C, is_current_join S T J.
Proof.
exact: (@current_pushforward_exists R h2 (n+(1+n))%N n (i+1+j)%N
  Domain Full hDomain hFull Chain F Image Smooth Proper).
Qed.

(** Source for [current_join_unique]: the original defining
    pushforward action determines the join, supporting Federer
    4.1.11, p. 364. The compact hypotheses supply genuine tests
    for every target test through the preceding properness theorem. *)
Theorem current_join_unique (J K : C) :
  is_current_join S T J -> is_current_join S T K -> J = K.
Proof.
exact: (@current_pushforward_unique R h2 (n+(1+n))%N n (i+1+j)%N
  Domain Full hDomain hFull Chain F Image Smooth Proper J K).
Qed.
End CurrentJoinExistence.
