(** Federer (1969), 4.1.1, p. 345: a compact test
    support meets only finitely many partition functions.
    The finite selection is proved from the original local
    finiteness and the existing compact-incidence theorem. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality reals topology.
From Federer Require Import RealNormUP NormMetric CompactSupportFunctionUP SmoothCompactSet
  SmoothCompactPartitionUP NormLocallyFiniteFunctionSupports LocallyFiniteFamilyCompact.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [smooth_partition_compact_active_selection]:
    a finite set contains every nonzero partition term on
    K, supporting the partial sums in Federer 4.1.1,
    p. 345. The actual compact K is retained. *)
Theorem smooth_partition_compact_active_selection (R:realType)
    (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
    (U:set X) (J:choiceType) (I:set J) (v:J->X->R)
    (hv:is_smooth_compact_partition hNX U I v)
    (K:smooth_compact_set hNX U):
  exists F:{fset J},(forall s,s \in F ->I s) /\
    forall x,smooth_compact_carrier K x ->forall s,I s ->s \notin F ->v s x=0.
Proof.
have hLocal:=@norm_locally_finite_function_supports R X NX hNX J U I v
  (smooth_partition_locally_finite hv).
have hFinite:=@locally_finite_family_compact (real_norm_metric_space hNX) J U I
  (fun s=>@real_function_support R (real_norm_metric_space hNX) (v s))
  (smooth_compact_carrier K) hLocal (smooth_compact_is_compact K) (smooth_compact_in_domain K).
pose Hit:set J:=I `&` [set s|exists x,smooth_compact_carrier K x /\
  @real_function_support R (real_norm_metric_space hNX) (v s) x].
pose F:=fset_set Hit.
exists F; split.
- move=>s; rewrite /F in_fset_set // =>/set_mem [hs hHit]; exact hs.
- move=>x hx s hs hn.
  case:(pselect (v s x=0))=>// hne.
  have hIn:s \in F.
    rewrite /F in_fset_set //; apply/mem_set; split=>//.
    exists x; split=>//; exact:(@subset_closure (real_norm_metric_space hNX) _ x hne).
  by move:hn; rewrite hIn.
Qed.
