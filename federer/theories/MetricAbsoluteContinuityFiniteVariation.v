(** Federer (1969), 2.10.13, p. 177, absolute-continuity criterion: absolute
    continuity implies finite variation on the stated interval. Generalise
    the already proved scalar finite-family argument of 2.9.20(3), pp.
    165–166, to endpoint distances in a metric space. No completeness or
    reflexivity is required for this supporting implication. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  constructive_ereal topology ring lra.
From Federer Require Import RealMetricBackground CurveVariationUP ExtendedRealBounds
  OrderedIntervalFamilyUP RealPartitionIntervalFamilies MetricCurveAbsoluteContinuityUP
  MetricIntervalFamilyNearVariation StieltjesIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [metric_family_increment_bound_variation]: supporting the
    absolute-continuity part of 2.10.13, p. 177, and the first consequent
    implication of (3) in Federer 2.9.20, p. 166 Every variation partition
    of [u,v] yields an eligible strict family of total length v-u, including
    when partition terms repeat. Taking the supremum gives the same epsilon
    bound for V_u^v g. *)
Lemma metric_family_increment_bound_variation (R : realType) (Y : metricType R) (g : R -> Y)
    (a b d e u v : R) :
  (forall s : seq (R * R), is_ordered_real_interval_family a b s ->
    real_interval_family_length s<=d -> metric_interval_family_increment_sum g s<=e) ->
  a<=u -> u<=v -> v<=b -> v-u<=d ->
  (curve_variation g u v<=e%:E)%E.
Proof.
move=> hfamily hau huv hvb hwidth.
apply: extended_real_sup_least=> z [s [[hs [hn [hh hl]]] ->]].
have hordered : is_ordered_real_interval_family a b (real_partition_interval_cells s).
  apply: real_partition_cells_ordered hs _ _.
  + have he : head a s=head u s by case: s hn hh hl=> [//|p s'].
    by rewrite he hh.
  + have he : last a s=last u s by case: s hn hh hl=> [//|p s'].
    by rewrite he hl.
have hlen : real_interval_family_length (real_partition_interval_cells s)<=d.
  by rewrite (@real_partition_cells_length R s u hs) hh hl.
have hb := hfamily _ hordered hlen.
by rewrite (@metric_partition_cells_increments R Y g s hs) in hb; rewrite lee_fin.
Qed.

(** Source for [metric_absolute_continuity_small_variation]: supporting
    2.10.13, p. 177, and the short-interval consequence of Federer
    2.9.20(3), p. 166 Absolute continuity supplies a uniform bound on total
    variation over every sufficiently short subinterval. This proves
    finiteness on those subintervals without a separate bounded-variation
    assumption. *)
Theorem metric_absolute_continuity_small_variation (R : realType) (Y : metricType R) (g : R -> Y)
    (a b : R) : is_absolutely_continuous_metric_curve g a b ->
  forall e : R, 0<e -> exists d : R, 0<d /\ forall u v : R,
    a<=u -> u<=v -> v<=b -> v-u<=d ->
    (curve_variation g u v<=e%:E)%E.
Proof.
move=> hg e he; have [d [hd hs]] := hg e he.
exists d; split=> // u v hau huv hvb hwidth.
exact: metric_family_increment_bound_variation hs hau huv hvb hwidth.
Qed.
(** Source for [metric_uniform_short_variation_sum_bound]: supporting
    2.10.13, p. 177, by finite subdivision argument for Federer 2.9.24, p.
    169, and 2.9.20, p. 166. If every subinterval of length at most d has
    variation at most one, n successive cells of width h<=d have variation
    at most n. Zero-width and zero-cell cases are included. *)
Lemma metric_uniform_short_variation_sum_bound (R : realType) (Y : metricType R) (g : R -> Y)
    (a b d h : R) : 0<=h -> h<=d ->
  (forall u v : R, a<=u -> u<=v -> v<=b -> v-u<=d ->
    (curve_variation g u v<=1)%E) ->
  forall (n : nat) (u : R), a<=u -> u+n%:R*h<=b ->
    (curve_variation g u (u+n%:R*h)<=n%:R%:E)%E.
Proof.
move=> hh hhd hsmall; elim=> [|n ih] u hau hub.
- by rewrite mul0r addr0 curve_variation_self.
- have hn0 : 0<=n%:R*h by rewrite mulr_ge0 // ler0n.
  have hend : u+n.+1%:R*h=u+h+n%:R*h.
    by rewrite -addn1 natrD mulrDl mul1r; ring.
  have huh : u<=u+h by lra.
  have huhb : u+h<=b by rewrite hend in hub; lra.
  have huhe : u+h-u<=d by lra.
  have hfirst := hsmall u (u+h) hau huh huhb huhe.
  have hrest := ih (u+h) (le_trans hau huh).
  rewrite hend in hub.
  have hR := hrest hub.
  have horder : u+h<=u+h+n%:R*h by lra.
  rewrite hend (@curve_variation_split R Y
    g u (u+h) (u+h+n%:R*h) huh horder).
  have hbnd := leeD hfirst hR.
  have hnE : ((1 : R)%:E+(n%:R : R)%:E)%E=(n.+1%:R : R)%:E.
    by rewrite -EFinD -[n.+1]addn1 natrD addrC.
  by rewrite hnE in hbnd.
Qed.

(** Source for [metric_absolute_continuity_finite_variation]: supporting
    2.10.13, p. 177: the finite variation implied by the printed absolute
    continuity hypothesis in Federer 2.9.24, p. 169. Neither continuity nor
    variation outside [a,b] is assumed. *)
Theorem metric_absolute_continuity_finite_variation (R : realType) (Y : metricType R) (g : R -> Y)
    (a b : R) : a<=b -> is_absolutely_continuous_metric_curve g a b ->
  (curve_variation g a b < +oo)%E.
Proof.
move=> hab hAC.
have [d [hd hsmall]] := metric_absolute_continuity_small_variation hAC ltr01.
have [n hn] := @uniform_mesh_small R a b d hab hd.
pose h := (b-a)/n.+1%:R.
have hh : 0<=h by rewrite /h divr_ge0 ?subr_ge0 ?ler0n.
have hhd : h<=d := ltW (hn n (leqnn n)).
have hend : a+n.+1%:R*h=b.
  by rewrite /h mulrC mulfVK ?pnatr_eq0 // addrC subrK.
have hb := @metric_uniform_short_variation_sum_bound R Y g a b d h hh hhd hsmall
  n.+1 a (lexx a).
rewrite hend in hb.
exact: le_lt_trans (hb (lexx b)) (ltry _).
Qed.
