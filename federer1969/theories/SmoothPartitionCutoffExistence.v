(** Federer (1969), 4.1.1, pp. 344–345: finite sums of
    the existing partition give smooth compact cutoffs equal
    to one on a neighbourhood of a prescribed compact set. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality reals topology.
From Federer Require Import RealNormUP NormMetric CompactSupportFunctionUP FiniteFamilySumUP
  SmoothCompactPartitionUP NormLocallyFiniteFunctionSupports LocallyFiniteCompactNeighbourhood
  SmoothPartitionFiniteSum SmoothCompactCutoffUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [smooth_partition_compact_cutoff_exists]: a
    finite part of a partition of unity is one throughout a
    neighbourhood of K and has compact support in U, supporting
    the dual support arguments in Federer 4.1.1, pp. 344–345,
    by the original 3.1.13 partition. *)
Theorem smooth_partition_compact_cutoff_exists (R:realType)
    (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
    (U K:set X) (J:choiceType) (I:set J) (v:J->X->R):
  @open (real_norm_metric_space hNX) U ->
  is_smooth_compact_partition hNX U I v ->
  compact [set x:real_norm_metric_space hNX|K x] ->K `<=` U ->
  exists chi:X->R,is_smooth_compact_cutoff hNX U K chi.
Proof.
move=>hU hv hK hKU.
have hLocal:=@norm_locally_finite_function_supports R X NX hNX J U I v (smooth_partition_locally_finite hv).
have [W [hW [hKW [hWU hFinite]]]]:=locally_finite_compact_open_neighbourhood hU hLocal hK hKU.
pose Hit:set J:=I `&` [set j|exists x,W x /\
  @real_function_support R (real_norm_metric_space hNX) (v j) x].
pose F:=fset_set Hit.
have hFI s:s \in F -> I s.
  move=>hs; move:hs; rewrite /F in_fset_set // =>/set_mem [hs hHit]; exact hs.
have hZero x (hx:W x) s (hs:I s) (hn:s \notin F):v s x=0.
  case:(pselect (v s x=0))=>// hne.
  have hIn:s \in F.
    rewrite /F in_fset_set //; apply/mem_set; split=>//.
    exists x; split=>//; exact:(@subset_closure (real_norm_metric_space hNX) _ x hne).
  by move:hn; rewrite hIn.
pose chi x:=\sum_(s:F) v (val s) x.
have hClass:=@smooth_partition_finite_sum_regular R X NX hNX U J I v hv F hFI.
have hBoundCompact:=@smooth_partition_finite_sum_support_compact R X NX hNX U J I v hv F hFI.
have hBoundDomain:=@smooth_partition_finite_sum_support_in_domain R X NX hNX U J I v hv F hFI.
have hSupport:=@smooth_partition_finite_sum_support R X NX hNX U J I v hv F hFI.
exists chi; constructor.
- exact hClass.
- apply:(subclosed_compact (@real_function_support_closed R (real_norm_metric_space hNX) chi)
    hBoundCompact); exact hSupport.
- exact:subset_trans hSupport hBoundDomain.
- exists W; split=>//; split=>// x hx.
  have hSum:=smooth_partition_sum_one hv (hWU x hx) hFI (hZero x hx).
  rewrite big_seq_fsetE in hSum; exact:esym hSum.
Qed.
