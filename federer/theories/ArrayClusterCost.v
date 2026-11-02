(** Federer (1969), 2.10.22, pp. 184–185:
    finite prefix costs pass to a compact-array limit,
    and the remaining source cost is bounded by the
    total budget minus the limiting prefix. The proof
    uses arbitrarily late rows in coordinate neighbourhoods,
    rather than a chosen diagonal subsequence. Source
    editions and the general-topology reference are recorded
    in CompactArrayCluster.v; these are supporting lemmas. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground NonnegativeSum NonnegativeSumRestriction
  ExtendedScaledErrorBound CompactArrayCluster.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_countable_array_cluster]: supporting
    finite-coordinate form of the compact extraction in
    2.10.22, pp. 184–185. It asserts a
    cluster property, without assuming any cost bound. *)
Definition is_countable_array_cluster (Y : topologicalType)
    (u : nat -> nat -> Y) (v : nat -> Y) :=
  forall (N : nat) (D : {fset nat}) (V : nat -> set Y),
    (forall k, k \in D -> nbhs (v k) (V k)) ->
    exists j, (N<=j)%N /\ forall k, k \in D -> V k (u j k).

(** Source for [array_cluster_remaining_cost_bound]: supporting
    finite-prefix and tail estimate in 2.10.22,
    p. 185. A finite error is kept explicitly;
    the source row also meets any prescribed finite
    collection of coordinate neighbourhoods. *)
Theorem array_cluster_remaining_cost_bound (R : realType) (Y : topologicalType)
    (w : Y -> R) (u : nat -> nat -> Y) (v : nat -> Y) (s : R) (err : nat -> R) :
  continuous (fun y => (w y : real_line_metric R)) ->
  is_countable_array_cluster u v ->
  (forall j k, 0<=w (u j k)) ->
  (forall j, (nonnegative_sum setT (fun k=>(w (u j k))%:E)<=(s+err j)%:E)%E) ->
  (forall e : R, 0<e -> exists N, forall j, (N<=j)%N -> err j<=e) ->
  forall (N : nat) (D E : {fset nat}) (V : nat -> set Y) (e : R),
  (forall k, k \in E -> nbhs (v k) (V k)) -> 0<e ->
  exists j, (N<=j)%N /\ (forall k, k \in E -> V k (u j k)) /\
    ((\sum_(k <- D) w (v k))%:E +
      nonnegative_sum (setT `\` [set` D]) (fun k=>(w (u j k))%:E)
      <=(s+(size D)%:R*e+e)%:E)%E.
Proof.
move=> hw hcluster h0 hbudget herr N D E V e hV he.
have [N0 hN0] := herr e he.
pose W k : set Y := [set y | `|w (v k)-w y|<e].
have hW k : nbhs (v k) (W k).
  have hb : nbhs (w (v k) : real_line_metric R) [set t | `|w (v k)-t|<e].
    apply: (proj2 (metricType_numDomainType.nbhs_mdistP (w (v k) : real_line_metric R) _)).
    exists e=> // y hy; exact hy.
  exact: hw (v k) _ hb.
pose U k := (if k \in D then W k else setT) `&` (if k \in E then V k else setT).
have hU k : k \in (fsetU D E) -> nbhs (v k) (U k).
  move=> hk; apply: filterI.
  - rewrite /U; case: ifP=> _; [exact: hW|exact: filterT].
  - case: ifP=> hkE; [exact: hV k hkE|exact: filterT].
have [j [hNj hj]] := hcluster (maxn N N0) ((fsetU D E)) U hU.
have hNj0 : (N0<=j)%N := leq_trans (leq_maxr N N0) hNj.
have hprefix : (\sum_(k <- D) w (v k)) <= (\sum_(k <- D) w (u j k))+(size D)%:R*e.
  have hconst : (\sum_(k <- D) e)=(size D)%:R*e.
    by rewrite big_seq_fsetE sumr_const cardT cardfE mulr_natl cardE.
  rewrite -hconst -big_split; rewrite !big_seq; apply: ler_sum=> k hk.
  have hUk : U k (u j k) by apply: hj; rewrite in_fsetU hk.
  have hWk : W k (u j k) by move: hUk.1; rewrite hk.
  have hh : w (v k)-w (u j k)<=e := le_trans (ler_norm _) (ltW hWk).
  change (is_true (w (v k)<=w (u j k)+e)); lra.
have h0e k : (0<=(w (u j k))%:E)%E by rewrite lee_fin; exact: h0.
have hpreE : ((\sum_(k <- D) w (v k))%:E<=((\sum_(k <- D) w (u j k))+(size D)%:R*e)%:E)%E by rewrite lee_fin.
have hsplit := @nonnegative_sum_split R [the choiceType of (nat : Type)] setT [set` D]
  (fun k=>(w (u j k))%:E) (fun k _=> h0e k).
rewrite setTI nonnegative_sum_finite in hsplit; last by move=> k hk; rewrite lee_fin; exact: h0.
rewrite sumEFin in hsplit.
exists j; split; first exact: leq_trans (leq_maxl N N0) hNj.
split.
- move=> k hk; have hUk : U k (u j k) by apply: hj; rewrite in_fsetU hk orbT.
  by move: hUk.2; rewrite hk.
- have hh := @leeD R _ _
    (nonnegative_sum (setT `\` [set` D]) (fun k=>(w (u j k))%:E))
    (nonnegative_sum (setT `\` [set` D]) (fun k=>(w (u j k))%:E))
    hpreE (lexx _).
  rewrite EFinD addeAC -hsplit in hh.
  apply: le_trans hh _.
  have htot := leeD (hbudget j) (lexx ((size D)%:R*e)%:E).
  apply: le_trans htot _; rewrite -!EFinD lee_fin.
  have hherr := hN0 j hNj0; lra.
Qed.

(** Source for [array_cluster_finite_cost_bound]: direct
    supporting limit of finite prefix costs in
    2.10.22, pp. 184–185: every finite
    collection of limiting costs is at most s. *)
Theorem array_cluster_finite_cost_bound (R : realType) (Y : topologicalType)
    (w : Y -> R) (u : nat -> nat -> Y) (v : nat -> Y) (s : R) (err : nat -> R) :
  continuous (fun y => (w y : real_line_metric R)) ->
  is_countable_array_cluster u v -> (forall j k, 0<=w (u j k)) ->
  (forall j, (nonnegative_sum setT (fun k=>(w (u j k))%:E)<=(s+err j)%:E)%E) ->
  (forall e : R, 0<e -> exists N, forall j, (N<=j)%N -> err j<=e) ->
  forall D : {fset nat}, (\sum_(k <- D) w (v k)<=s)%R.
Proof.
move=> hw hcluster h0 hb herr D.
have hsize : (0<=(size D)%:R+1 :> R) by rewrite addr_ge0 ?ler0n //.
have hh : ((\sum_(k <- D) w (v k))%:E<=s%:E)%E.
  apply: (@extended_upper_bound_from_scaled_errors R _ s ((size D)%:R+1) hsize)=> e he.
  have [j [_ [_ hj]]] := @array_cluster_remaining_cost_bound R Y w u v s err hw hcluster h0 hb herr
    0%N D fset0 (fun _=>setT) e (fun k hk=>@filterT Y (nbhs (v k)) (nbhs_filter (v k))) he.
  have hle : ((\sum_(k <- D) w (v k))%:E<=
      (\sum_(k <- D) w (v k))%:E+nonnegative_sum (setT `\` [set` D]) (fun k=>(w (u j k))%:E))%E.
    have hz := leeD (lexx ((\sum_(k <- D) w (v k))%:E))
      (nonnegative_sum_nonnegative (setT `\` [set` D]) (fun k=>(w (u j k))%:E)).
    by rewrite adde0 in hz.
  have hfinal := le_trans hle hj; rewrite mulrDl mul1r addrA; exact hfinal.
by move: hh; rewrite lee_fin.
Qed.
