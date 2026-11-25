(** Federer (1969), 3.2.46, p. 281: concatenate genuine
    Lipschitz curves to prove the triangle inequality. The
    translated second parameter keeps its original duration;
    the joining value is required to be the same actual point. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring
  classical_sets topology.
From Federer Require Import RealMetricBackground LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_curve_concatenation]: the usual joined
    curve supporting the triangle inequality in Federer 3.2.46,
    p. 281. The second interval's initial parameter c is moved
    to the first interval's final parameter b. *)
Definition metric_curve_concatenation (R : realType) (Y : Type)
    (C D : R -> Y) (b c t : R) :=
  if t <= b then C t else D (t-b+c).

(** Source for [metric_curve_concatenation_lipschitz]: the
    actual joined curve is Lipschitz, supporting the triangle
    argument in Federer 3.2.46, p. 281. The sum of the two
    bounds suffices; both may vanish. *)
Lemma metric_curve_concatenation_lipschitz (R : realType) (Y : metricType R)
    (C D : real_line_metric R -> Y) b c L M :
  @is_metric_lipschitz_bound R [the metricType R of real_line_metric R] Y setT C L ->
  @is_metric_lipschitz_bound R [the metricType R of real_line_metric R] Y setT D M ->
  C b = D c ->
  @is_metric_lipschitz_bound R [the metricType R of real_line_metric R] Y setT
    (metric_curve_concatenation C D b c) (L+M).
Proof.
move=> hC hD hJoin; split; first exact: addr_ge0 hC.1 hD.1.
have hCross t u : t <= b -> b <= u ->
    mdist (C t) (D (u-b+c)) <= (L+M)*`|t-u|.
  move=> htb hbu.
  have h1 := hC.2 t b Logic.I Logic.I.
  have h2 := hD.2 c (u-b+c) Logic.I Logic.I.
  have hAbs1 : `|t-b| = b-t by rewrite ler0_norm ?subr_le0 // opprB.
  have hAbs2 : `|c-(u-b+c)| = u-b.
    have he : c-(u-b+c) = -(u-b) by ring.
    by rewrite he normrN ger0_norm ?subr_ge0.
  have hAbs : `|t-u| = u-t.
    rewrite ler0_norm ?subr_le0; first exact: opprB.
    exact: le_trans htb hbu.
  rewrite real_line_metric_distanceE hAbs1 in h1.
  rewrite real_line_metric_distanceE hAbs2 in h2.
  have ht := metric_triangle (C t) (C b) (D (u-b+c)).
  rewrite hJoin in h1 ht.
  have hLength := le_trans ht (lerD h1 h2).
  rewrite hAbs; have hL := hC.1; have hM := hD.1; nra.
move=> t u _ _.
case: (leP t b)=> htb; case: (leP u b)=> hub.
- rewrite /metric_curve_concatenation htb hub.
  apply: le_trans (hC.2 t u Logic.I Logic.I) _.
  have hInc : L <= L+M by have hM := hD.1; lra.
  exact (ler_wpM2r (mdist_ge0 (t : real_line_metric R) u) hInc).
- rewrite /metric_curve_concatenation htb (lt_geF hub).
  exact: hCross t u htb (ltW hub).
- rewrite /metric_curve_concatenation (lt_geF htb) hub metric_sym
    real_line_metric_distanceE distrC.
  exact: hCross u t hub (ltW htb).
- rewrite /metric_curve_concatenation (lt_geF htb) (lt_geF hub).
  have hh := hD.2 (t-b+c) (u-b+c) Logic.I Logic.I.
  have he : (t-b+c)-(u-b+c)=t-u by ring.
  rewrite real_line_metric_distanceE he in hh.
  apply: le_trans hh _; rewrite real_line_metric_distanceE.
  have hInc : M <= L+M by have hL := hC.1; lra.
  exact (ler_wpM2r (normr_ge0 (t-u)) hInc).
Qed.
