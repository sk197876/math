(** General topology supporting Federer (1969), 2.2.4, p. 62: the countable
    base used to bound the family of closed subsets and to obtain a perfect
    condensation kernel. We prove it from countably many dense centers and
    shrinking positive radii, including the empty metric space. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals topology.
From Federer Require Import MetricClosedBalls SeparableClosedCover SequencePowerBounds
  CountableFamilyEnumeration CountableOpenBaseUP CountableBaseNormalizationConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [separable_metric_countable_base_exists]: supporting metric
    countable-base theorem for Federer 2.2.4, p. 62. The enumeration
    includes an empty member by normalization; this does not impose
    nonemptiness on the metric space. *)
Theorem separable_metric_countable_base_exists (R : realType) (T : metricType R)
    (D : set T) : countable D -> dense D ->
  exists U : nat -> set T, is_countable_open_base U.
Proof.
move=> hc hd; case: (pselect (exists x : T, True))=> [[x0 _]|he].
- pose J := D `*` (@setT nat).
  pose B (p : T * nat) := [set x | mdist p.1 x < (2^-1 : R)^+p.2].
  have hJ : countable J by apply: countableX=> //; exact: countableP.
  have hJn : exists p, J p.
    have [c [hDc _]] := metric_dense_point_near hd x0 (@ltr01 R).
    exists (c,0%N); by split.
  have [V hV] := countable_nonempty_family_enumeration B hJ hJn.
  apply: (@normalized_countable_base_exists T V).
  + move=> i; have hm : (V @` setT) (V i) by exists i.
    rewrite hV in hm; have [p hp <-] := hm; exact: metric_open_ball_open.
  + move=> O hO x hx.
    have hn : nbhs x O by rewrite openE in hO; exact: hO x hx.
    have [e hepos heb] := proj1 (metricType_numDomainType.nbhs_mdistP x O) hn.
    have he2 : 0 < e/2 by rewrite divr_gt0 // ltr0n.
    have [k hk] := sequence_inverse_power_small he2.
    pose r := (2^-1 : R)^+k.
    have hr : 0 < r by rewrite /r exprn_gt0 // invr_gt0 ltr0n.
    have [c [hDc hcx]] := metric_dense_point_near hd x hr.
    have hm : (B @` J) (B (c,k)) by exists (c,k)=> //; split.
    rewrite -hV in hm; have [i _ hi] := hm.
    exists i; rewrite hi; split.
    * change (mdist c x < r); by rewrite metric_sym.
    * move=> y hy; apply: heb.
      have ht : mdist x y < r+r.
        apply: le_lt_trans (metric_triangle x c y) _; exact: ltrD hcx hy.
      apply: lt_trans ht _; have hh := ltrD hk hk; by rewrite -splitr in hh.
- exists (fun _ => set0); constructor.
  + move=> i; exact: open0.
  + by [].
  + move=> V hV x hx; exfalso; apply: he; by exists x.
Qed.
