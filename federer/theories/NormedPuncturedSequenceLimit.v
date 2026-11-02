(** Federer (1969), 2.9.22, pp. 167–168: measurable norm derivatives used in
    the vector-integral extension. Restrict an already existing punctured
    norm limit to positive reciprocal increments; this never infers a
    two-sided derivative from a single sequence limit. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import RealNormUP NormMetric NormedCurveDerivativeUP ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [punctured_norm_limit_reciprocal_sequence]: supporting
    measurable norm derivative step in Federer 2.9.22, pp. 167–168.
    The positive increments 1/(n+1) eventually lie inside every
    punctured cutoff. Norm symmetry gives convergence in the actual
    norm metric to the already specified limit. *)
Lemma punctured_norm_limit_reciprocal_sequence (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (u : R -> E) (v : E) :
  punctured_norm_limit N u v ->
  (fun n => (u ((n.+1%:R : R)^-1) : real_norm_metric_space hN)) @ \oo -->
    (v : real_norm_metric_space hN).
Proof.
move=> hu; apply/cvg_ballP=> e he.
have [d [hd hB]] := hu e he.
have [n hn] := positive_reciprocal_nat_small hd.
exists n=> // m hnm.
have hmp : 0<(m.+1%:R : R)^-1 by rewrite invr_gt0 ltr0n.
have hle : (m.+1%:R : R)^-1<=(n.+1%:R : R)^-1.
  rewrite lef_pV2.
  - by rewrite ler_nat -[n.+1]addn1 -[m.+1]addn1 leq_add2r.
  - change (0<(m.+1%:R : R)); by rewrite ltr0n.
  - change (0<(n.+1%:R : R)); by rewrite ltr0n.
have hsmall : 0<`|(m.+1%:R : R)^-1|<d.
  rewrite (ger0_norm (ltW hmp)); apply/andP; split=> //; exact: le_lt_trans hle hn.
have hh := hB _ hsmall.
change (N (v-u ((m.+1%:R : R)^-1))<e).
by rewrite (real_seminorm_subtract hN.1).
Qed.
