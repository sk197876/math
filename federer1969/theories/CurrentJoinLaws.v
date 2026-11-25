(** Federer (1969), 4.1.11, p. 364: the original join is
    the stated proper pushforward and has compact support. These
    laws use only the independent specification and opaque public
    operations. The original currents gain no mass hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  CurrentDensityUP CurrentPushforwardUP CurrentPushforwardSealed
  CurrentPushforwardSupport CurrentPushforwardNormality CurrentAboveDimension
  CurrentJoinMapSealed CurrentJoinMapClass CurrentJoinDomain
  CurrentJoinSourceChain CurrentJoinSourceCompact CurrentJoinUP
  CurrentJoinExistence CurrentJoinSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentJoinLaws.
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
Local Notation J := (@CurrentJoin.value R h2 n i j S T hS hT).
Local Notation Push :=
  (@CurrentPushforward.value R h2 (n+(1+n))%N n (i+1+j)%N
    Domain Full hDomain hFull Chain F Image Smooth Proper).

(** Source for [current_join_pushforward]: the original
    S join T is F#(S times [0,1] times T), Federer 4.1.11,
    p. 364, defining display. Derive equality from both public
    action laws; neither sealed witness is unfolded. *)
Theorem current_join_pushforward : J = Push.
Proof.
apply: (@current_join_unique R h2 n i j S T hS hT).
- exact: CurrentJoin.laws.
- exact: CurrentPushforward.laws.
Qed.

(** Source for [current_join_compact]: the original join of
    compactly supported currents is compactly supported, supporting
    the simplex recursion in Federer 4.1.11, pp. 364–365. *)
Theorem current_join_compact :
  @compact (real_norm_metric_space hNX)
    (@current_support R h2 n Full hFull (i+1+j)%N J).
Proof.
rewrite current_join_pushforward.
exact: (@current_pushforward_compact_support R h2 (n+(1+n))%N n
  Domain Full hDomain hFull F Image Smooth (i+1+j)%N Chain Proper
  (@current_join_source_compact R h2 n i j S T hS hT)).
Qed.

(** Source for [current_join_support_image]: the original
    join support lies in F(spt(S times [0,1] times T)), supporting
    the compact join and simplex assertions of Federer 4.1.11,
    pp. 364–365. Cancellation may make the inclusion strict. *)
Theorem current_join_support_image :
  @current_support R h2 n Full hFull (i+1+j)%N J `<=`
    F @` (@current_support R h2 (n+(1+n))%N Domain hDomain
      (i+1+j)%N Chain).
Proof.
rewrite current_join_pushforward.
exact: (@current_pushforward_support_image R h2 (n+(1+n))%N n
  (i+1+j)%N Domain Full hDomain hFull Chain F Image Smooth Proper).
Qed.

(** Source for [current_join_proof_independent]: the original
    join depends on its currents, not on their compactness proofs,
    supporting the unambiguous notation in Federer 4.1.11, p. 364. *)
Theorem current_join_proof_independent
    (hS' : @compact (real_norm_metric_space hNX)
      (@current_support R h2 n Full hFull i S))
    (hT' : @compact (real_norm_metric_space hNX)
      (@current_support R h2 n Full hFull j T)) :
  J = @CurrentJoin.value R h2 n i j S T hS' hT'.
Proof.
apply: (@current_join_unique R h2 n i j S T hS hT);
  exact: CurrentJoin.laws.
Qed.

(** Source for [current_join_above_dimension]: the original
    degree i+1+j current is zero above ambient dimension,
    supporting Federer 4.1.11, pp. 364–366, by the preceding
    dimension observation in 4.1.10, p. 364. *)
Theorem current_join_above_dimension : (n<i+1+j)%N -> J = 0.
Proof.
move=> hDegree.
exact: (@current_above_dimension R h2 n (i+1+j)%N hDegree
  Full hFull J).
Qed.
End CurrentJoinLaws.
