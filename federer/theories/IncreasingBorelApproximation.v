(** Federer (1969), 2.10.24, p. 187: supporting construction of increasing
    Borel B_j from finite-stage Borel approximants with summable losses.
    Intersect the tail approximants; outside the null set of infinitely many
    losses, every point of the increasing source union eventually lies in
    all approximants. This expands the printed B_j choice using only the
    project's measure laws. Source context: WeightedMetricEnvelopeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureAlmostBasic NonnegativeSum SummableExceptionalSets TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [increasing_borel_approximation_from_losses]: supporting
    increasing Borel family in 2.10.24,
    p. 187. The source sets need not be
    measurable; summability of their exceptional losses
    gives the required almost-everywhere covering. *)
Theorem increasing_borel_approximation_from_losses (R : realType) (X : topologicalType)
    (mu : set X -> \bar R) (A C : nat -> set X) :
  is_measure mu -> (forall n, borel_set (C n)) ->
  (forall n, C n `<=` A n) ->
  (forall n m, (n<=m)%N -> A n `<=` A m) ->
  nonnegative_sum setT (fun n=>mu (A n `\` C n))< +oo ->
  exists B : nat -> set X,
    (forall n, borel_set (B n)) /\
    (forall n m, (n<=m)%N -> B n `<=` B m) /\
    (forall n, B n `<=` C n) /\ mu ((\bigcup_n A n) `\` \bigcup_n B n)=0.
Proof.
move=> hm hC hCA hinc hsum.
pose E n := A n `\` C n.
pose Z := \bigcap_N \bigcup_(n in [set n | (N<=n)%N]) E n.
have hZ : mu Z=0 := measure_summable_exceptional_limsup_null hm hsum.
pose B n := \bigcap_(k in [set k | (n<=k)%N]) C k.
have hB n : borel_set (B n).
  apply: (@borel_set_countable_intersection X [the choiceType of (nat : Type)] [set k | (n<=k)%N] C (countableP _)).
  - exists n; exact: leqnn.
  - by move=> k hk; exact: hC.
have hBinc n m (hnm : (n<=m)%N) : B n `<=` B m.
  move=> x hx k hk; apply: hx; exact: leq_trans hnm hk.
have hBC n : B n `<=` C n by move=> x hx; exact: hx n (leqnn n).
have hnull : mu ((\bigcup_n A n) `\` \bigcup_n B n)=0.
  apply: (@measure_null_subset R X mu hm _ Z _ hZ).
  move=> x [[n _ hxn] hxB] N _.
  have [k [hMk hxC]] : exists k, (maxn N n<=k)%N /\ ~ C k x.
    apply: contrapT=> hnone; apply: hxB; exists (maxn N n)=> // j hj.
    apply: contrapT=> hxC; apply: hnone; exists j; by split.
  exists k; first exact: leq_trans (leq_maxl N n) hMk.
  split=> //; exact: hinc n k (leq_trans (leq_maxr N n) hMk) x hxn.
exists B; by split=> //; split=> //; split.
Qed.
