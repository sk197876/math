(** Federer (1969), 4.1.1, p. 344: an auxiliary
    compact neighbourhood exhaustion follows from the
    original countable smooth partition of 3.1.13,
    p. 225. Finite unions of original supports
    retain the source norm and the whole open domain. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp functions classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormRegularity NormClassZeroNonzeroLocus
  CompactSupportFunctionUP CompactFiniteCover SmoothCompactSet SmoothCompactPartitionUP
  SmoothPartitionFiniteSum CountableFiniteExhaustionUP NormLocallyFiniteFamilyUP FiniteFamilySumUP
  SmoothCompactExhaustionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section PartitionCompactExhaustion.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variable U:set X.
Hypothesis hU:@open (real_norm_metric_space hNX) U.
Variable J:choiceType.
Variable I:set J.
Variable v:J->X->R.
Hypothesis hv:is_smooth_compact_partition hNX U I v.
Variable C:nat->{fset J}.
Hypothesis hC:is_countable_finite_exhaustion I C.
Local Notation XN := (real_norm_metric_space hNX).

(** Source for [smooth_partition_exhaustion_compacts]:
    finite unions of original compact partition supports,
    supporting the compact neighbourhood bounds in
    Federer 4.1.1, p. 344. *)
Definition smooth_partition_exhaustion_compacts m:smooth_compact_set hNX U:=
  @Build_smooth_compact_set R X NX hNX U
    (@smooth_partition_finite_sum_support_bound R X NX hNX J v (C m))
    (@smooth_partition_finite_sum_support_in_domain R X NX hNX U J I v hv (C m)
      (@finite_exhaustion_subset J I C hC m))
    (@smooth_partition_finite_sum_support_compact R X NX hNX U J I v hv (C m)
      (@finite_exhaustion_subset J I C hC m)).

(** Source for [smooth_partition_exhaustion_open_sets]:
    original nonzero partition loci give open subsets
    of the finite compact unions, supporting Federer
    4.1.1, p. 344. *)
Definition smooth_partition_exhaustion_open_sets m:set XN:=
  U `&` \bigcup_(s in [set` (C m)]) [set x:XN|True /\ v s x!=0].

(** Source for [smooth_partition_exhaustion_open]: the
    auxiliary inner neighbourhoods are open in the
    original source norm, supporting Federer
    4.1.1, p. 344. *)
Lemma smooth_partition_exhaustion_open m:@open XN (smooth_partition_exhaustion_open_sets m).
Proof.
apply:openI hU _; apply:bigcup_open=>s hs.
apply:(@norm_class_zero_nonzero_locus_open R X R^o NX (fun t:R^o=>`|t|) hNX
  (@scalar_absolute_value_norm R) (fun _=>True) (v s)).
exact:(norm_class_continuous (@smooth_partition_global_class R X NX hNX U J I v hv s
  (@finite_exhaustion_subset J I C hC m s hs) 0%N)).
Qed.

(** Source for [smooth_partition_exhaustion_inner]: each
    open neighbourhood is contained in the corresponding
    original compact union, supporting Federer
    4.1.1, p. 344. *)
Lemma smooth_partition_exhaustion_inner m:
  smooth_partition_exhaustion_open_sets m `<=` smooth_compact_carrier (smooth_partition_exhaustion_compacts m).
Proof.
move=>x [hx [s hs [_ hne]]].
exists ([` hs]%fset); first by [].
apply:(@subset_closure XN _ x); apply/eqP; exact hne.
Qed.

(** Source for [smooth_partition_exhaustion_compact_monotone]:
    the compact bounds increase, supporting the
    common-support argument in Federer 4.1.1,
    p. 344. *)
Lemma smooth_partition_exhaustion_compact_monotone m n:(m<=n)%N ->
  smooth_compact_carrier (smooth_partition_exhaustion_compacts m) `<=`
  smooth_compact_carrier (smooth_partition_exhaustion_compacts n).
Proof.
move=>hmn x [s _ hs].
have hIn:val s \in C n:=(fsubsetP (@finite_exhaustion_increasing J I C hC m n hmn)) (val s) (valP s).
exists ([` hIn]%fset); first by [].
exact hs.
Qed.

(** Source for [smooth_partition_exhaustion_open_monotone]:
    the auxiliary open neighbourhoods increase with the
    original finite index exhaustion, supporting Federer
    4.1.1, p. 344. *)
Lemma smooth_partition_exhaustion_open_monotone m n:(m<=n)%N ->
  smooth_partition_exhaustion_open_sets m `<=` smooth_partition_exhaustion_open_sets n.
Proof.
move=>hmn x [hx [s hs hvx]]; split=>//; exists s; last exact hvx.
exact:((fsubsetP (@finite_exhaustion_increasing J I C hC m n hmn)) s hs).
Qed.

(** Source for [smooth_partition_exhaustion_covers]: the
    inner neighbourhoods cover U because the partition
    sum is one, supporting Federer 4.1.1,
    p. 344. *)
Lemma smooth_partition_exhaustion_covers x:U x ->
  exists n,smooth_partition_exhaustion_open_sets n x.
Proof.
move=>hx.
have [F [hFI hZero]]:=@norm_locally_finite_active_family R X R^o J NX U I v (smooth_partition_locally_finite hv) x hx.
have hOne:=smooth_partition_sum_one hv hx hFI hZero.
have hSome:exists s,s \in F /\ v s x<>0.
  case:(pselect (exists s,s \in F /\ v s x<>0))=>// hNone.
  have hSum:(\sum_(s<-F) v s x)=0.
    apply:big1_seq=>s hs.
    case:(pselect (v s x=0))=>// hn.
    exact:False_ind _ (hNone (ex_intro _ s (conj hs hn))).
  rewrite hSum in hOne.
  have hNonzero:(1:R)<>0.
    move=>hz; have hn:=@oner_neq0 R.
    by rewrite hz eqxx in hn.
  exact:False_ind _ (hNonzero hOne).
have [s [hs hne]]:=hSome.
have [n hn]:=@finite_exhaustion_cover J I C hC s (@hFI s hs).
exists n; split=>//; exists s=>//; split; first exact Logic.I; apply/eqP; exact hne.
Qed.

(** Source for [smooth_partition_compact_exhaustion_laws]:
    every original compact has a neighbourhood in a
    finite compact partition union, supporting the common-
    support assertion in Federer 4.1.1, p. 344. *)
Theorem smooth_partition_compact_exhaustion_laws:
  is_smooth_compact_exhaustion smooth_partition_exhaustion_compacts.
Proof.
constructor; first exact:smooth_partition_exhaustion_compact_monotone.
move=>K.
have hCover:smooth_compact_carrier K `<=` \bigcup_(n in (@setT nat)) smooth_partition_exhaustion_open_sets n.
  move=>x hx; have [n hn]:=smooth_partition_exhaustion_covers (smooth_compact_in_domain K x hx).
  by exists n.
have [F hFT hFCover]:=@compact_open_finite_cover XN [the choiceType of (nat:Type)] setT
  smooth_partition_exhaustion_open_sets (smooth_compact_carrier K) (smooth_compact_is_compact K)
  (fun n _=>@smooth_partition_exhaustion_open n) hCover.
pose N:=\max_(s:F) val s.
exists N,(smooth_partition_exhaustion_open_sets N); split; first exact:smooth_partition_exhaustion_open.
split; last exact:smooth_partition_exhaustion_inner.
move=>x hx; have [n hn hxn]:=hFCover x hx.
have hle:(n<=N)%N:=leq_bigmax ([` hn]%fset).
exact:(smooth_partition_exhaustion_open_monotone hle hxn).
Qed.
End PartitionCompactExhaustion.
