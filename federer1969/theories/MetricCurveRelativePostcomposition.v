(** Federer (1969), 3.2.7, p. 246: supporting
    localisation of the Lipschitz composition law of
    2.9.22, pp. 167–168. Only the range of
    the given compact parameter interval is needed. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology lra.
From Federer Require Import MetricCurveAbsoluteContinuityUP OrderedIntervalFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_family_relative_postcomposition_bound]:
    supporting the absolute continuity assertion in the
    third example of Federer 3.2.7, p. 246.
    A Lipschitz estimate on the relevant parameter
    range bounds every eligible finite family of increments. *)
Lemma metric_family_relative_postcomposition_bound (R:realType) (X Y:metricType R)
    (f:X->Y) (g:R->X) (L a b:R):
  (forall u v,a<=u<=b -> a<=v<=b ->
    mdist (f (g u)) (f (g v))<=L*mdist (g u) (g v)) ->
  forall s,is_ordered_real_interval_family a b s ->
  metric_interval_family_increment_sum (fun t=>f (g t)) s<=
    L*metric_interval_family_increment_sum g s.
Proof.
move=>h s hs.
rewrite /metric_interval_family_increment_sum mulr_sumr !big_seq.
apply:ler_sum=>[[u v] huv].
have [hau [huv' hvb]]:=ordered_real_interval_family_cell_bounds hs huv.
apply:h; apply/andP; split=>//; exact (le_trans (ltW huv') hvb) || exact (le_trans hau (ltW huv')).
Qed.

(** Source for [metric_absolute_continuity_relative_postcomposition]:
    compact-range version of 2.9.22, pp. 167–168,
    used for the cubic parameter of Federer 3.2.7,
    p. 246. No global Lipschitz extension or
    additional regularity of the outer map is required. *)
Theorem metric_absolute_continuity_relative_postcomposition (R:realType) (X Y:metricType R)
    (f:X->Y) (g:R->X) (L a b:R):
  0<=L ->
  (forall u v,a<=u<=b -> a<=v<=b ->
    mdist (f (g u)) (f (g v))<=L*mdist (g u) (g v)) ->
  is_absolutely_continuous_metric_curve g a b ->
  is_absolutely_continuous_metric_curve (fun t=>f (g t)) a b.
Proof.
move=>hL hf hg e he.
have hpos:0<L+1 by lra.
have hep:0<e/(L+1) by rewrite divr_gt0.
have [d [hd hb]]:=hg (e/(L+1)) hep.
exists d; split=>// s hs hlen.
have hCost:=metric_family_relative_postcomposition_bound hf hs.
have hSmall:=ler_wpM2l hL (hb s hs hlen).
have hLast:L*(e/(L+1))<=e.
  rewrite mulrA ler_pdivrMr // mulrDr mulr1 [L*e]mulrC lerDl.
  exact:ltW he.
exact (le_trans hCost (le_trans hSmall hLast)).
Qed.
