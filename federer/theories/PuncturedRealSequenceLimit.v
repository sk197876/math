(** Supporting scalar-sequence consequence of the actual derivative limit in
    Federer (1969), 2.9.22, p. 167, used to prove measurability of scalar
    derivatives. The derivative remains the two-sided punctured limit; a
    positive reciprocal sequence is used only after that limit is known. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals topology.
From Federer Require Import RealMetricBackground RealCurveDerivativeUP ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [punctured_real_limit_reciprocal_sequence]:
    supporting measurability step in Federer 2.9.22, p. 167.
    An actual finite punctured limit restricts to the sequence
    h_n=1/(n+1), which is positive and eventually smaller
    than every positive cutoff by the Archimedean property. *)
Lemma punctured_real_limit_reciprocal_sequence (R : realType) (u : R -> R) v :
  punctured_real_limit u v ->
  (fun n => (u ((n.+1%:R : R)^-1) : real_line_metric R)) @ \oo --> (v : real_line_metric R).
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
change (`|v-u ((m.+1%:R : R)^-1)|<e).
by rewrite distrC.
Qed.
