(** Federer (1969), 3.2.13, p. 250: the
    square substitution is absolutely continuous on
    each compact interval. This supporting finite-family
    criterion derives absolute continuity from a
    Lipschitz bound required only on that interval. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology lra ring.
From Federer Require Import RealMetricBackground OrderedIntervalFamilyUP MetricCurveAbsoluteContinuityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_interval_lipschitz_absolute_continuity]: the
    finite-interval absolute continuity needed for the
    square substitution in Federer 3.2.13,
    p. 250, by condition 2.9.20(3),
    p. 165. No global Lipschitz bound is assumed. *)
Lemma scalar_interval_lipschitz_absolute_continuity (R:realType) (g:R->R) (L a b:R):
  0<=L ->(forall x y,a<=x<=b ->a<=y<=b ->`|g x-g y|<=L*`|x-y|) ->
  is_absolutely_continuous_metric_curve (g:R->real_line_metric R) a b.
Proof.
move=>hL hLip e he.
have hDen:0<L+1 by lra.
have hd:0<e/(L+1) by rewrite divr_gt0.
exists (e/(L+1)); split=>// s hs hLen.
have hFamily:metric_interval_family_increment_sum (g:R->real_line_metric R) s<=
    L*real_interval_family_length s.
  rewrite /metric_interval_family_increment_sum /real_interval_family_length mulr_sumr !big_seq.
  apply:ler_sum=>[[u v]] hMem.
  have [hau [huv hvb]]:=ordered_real_interval_family_cell_bounds hs hMem.
  have hu:a<=u<=b by apply/andP; split=>//; exact:le_trans (ltW huv) hvb.
  have hv:a<=v<=b by apply/andP; split=>//; exact:le_trans hau (ltW huv).
  have hh:=hLip u v hu hv.
  have hNonnegative:0<=v-u by rewrite subr_ge0; exact:ltW huv.
  rewrite (distrC u v) (ger0_norm hNonnegative) in hh.
  exact hh.
have hCompare:=ler_wpM2l hL hLen.
have hLast:L*(e/(L+1))<=e.
  rewrite mulrA ler_pdivrMr // mulrDr mulr1 [L*e]mulrC lerDl; exact:ltW he.
exact (le_trans hFamily (le_trans hCompare hLast)).
Qed.
