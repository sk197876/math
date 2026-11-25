(** Federer (1969), 2.10.22, pp. 184–185: extract simultaneous limit
    generators from compact bounded Hausdorff families. Federer cites
    Kelley, General Topology, p. 238, Problem D(a), the diagonal process for
    countably many sequentially compact spaces. Use instead compactness of
    the product and a cluster point of the source sequence; finite
    coordinate neighbourhoods with arbitrarily late source indices suffice
    for the same proof. Kelley edition: Dover 2017 reprint of 1955, local
    library copy recorded in docs/references/README.md. This is
    general-topology background, not an additional measure-theoretic
    assumption. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [compact_countable_array_cluster]: supporting
    compact extraction in 2.10.22, pp. 184–185.
    Every finite collection of coordinate neighbourhoods
    is met by arbitrarily late source rows. This
    replaces a globally chosen diagonal subsequence,
    while retaining the printed finite-prefix uses. *)
Theorem compact_countable_array_cluster (Y : topologicalType) (K : set Y)
    (u : nat -> prod_topology (fun _ : nat => Y)) :
  compact K -> (forall j k, K (u j k)) ->
  exists v : prod_topology (fun _ : nat => Y),
    (forall k, K (v k)) /\
    forall (N : nat) (D : {fset nat}) (V : nat -> set Y),
      (forall k, k \in D -> nbhs (v k) (V k)) ->
      exists j, (N<=j)%N /\ forall k, k \in D -> V k (u j k).
Proof.
move=> hK hu.
pose P := prod_topology (fun _ : nat => Y).
pose A : set P := [set v | forall k, K (v k)].
have hA : compact A := @tychonoff [the choiceType of (nat : Type)] (fun _=>Y) (fun _=>K) (fun _=>hK).
pose F : set_system P := u @ eventually.
have PF : ProperFilter F by exact: fmap_proper_filter.
have hFA : F A.
  change (eventually [set j | A (u j)]); exists 0%N=> // j hj; exact: hu j.
have [v [hv hcluster]] := hA F PF hFA.
exists v; split; first exact hv.
move=> N D V hV.
pose W : set P := \bigcap_(k in [set` D]) [set q | V k (q k)].
have hW : nbhs v W.
  apply: (@filter_bigI P [the choiceType of (nat : Type)] D
    (fun k=>[set q : P | V k (q k)]) (nbhs v) (nbhs_filter v))=> k hk.
  exact: (@proj_continuous [the choiceType of (nat : Type)] (fun _=>Y) k v (V k) (hV k hk)).
pose B : set P := [set q | exists j, (N<=j)%N /\ q=u j].
have hB : F B.
  change (eventually [set j | B (u j)]); exists N=> // j hj; exists j; by split.
have [q [[j [hNj hq]] hqW]] := hcluster B W hB hW.
exists j; split=> // k hk; rewrite -hq; exact: hqW k hk.
Qed.
