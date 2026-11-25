(** General metric background for the bounded linear extension in
    Federer (1969), 4.1.14, p. 371, using the Cauchy-filter
    completeness of 2.2.8, p. 64. This auxiliary construction serves
    only the proof of existence of the independently specified map. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology lra.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP
  BanachDenseLinearExtensionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DenseApproximationFilter.
Variable R:realType.
Variables A V:lmodType R.
Variable NV:V->R.
Variable i:Hom A V.

(** Source for [dense_norm_approximation_filter]: approach an
    original point through the dense source, supporting the
    extension in Federer 4.1.14, p. 371. The explicit epsilon
    family uses no norm or completeness of A. *)
Definition dense_norm_approximation_filter (v:V):set_system A:=
  fun P=>exists epsilon:R,0<epsilon /\
    forall a,NV (v-i a)<epsilon->P a.

(** Source for [dense_norm_approximation_filter_laws]: the
    neighbourhood approximation family is a filter, the general
    topology underlying Federer 4.1.14, p. 371. *)
Lemma dense_norm_approximation_filter_laws v:
  Filter (dense_norm_approximation_filter v).
Proof.
constructor.
- exists 1;split;first exact:ltr01.
  by move=>a _.
- move=>P Q [e [he hP]] [d [hd hQ]].
  exists (Num.min e d);split;first by rewrite lt_min he hd.
  move=>a ha;split.
  + apply:hP;apply:(lt_le_trans ha).
    by rewrite ge_min lexx orTb.
  + apply:hQ;apply:(lt_le_trans ha).
    by rewrite ge_min lexx orbT.
- move=>P Q hPQ [e [he hP]].
  exists e;split;first exact:he.
  move=>a ha;exact:hPQ _ (hP a ha).
Qed.

(** Source for [dense_norm_approximation_filter_proper]: density
    makes the approximation filter proper, supporting the complete
    target limit in Federer 4.1.14, p. 371. *)
Lemma dense_norm_approximation_filter_proper:
  is_norm_dense_linear_image NV i->forall v,
  ProperFilter (dense_norm_approximation_filter v).
Proof.
move=>hDense v;constructor.
- move=>[e [he hEmpty]].
  have[a ha]:=hDense v e he.
  exact:hEmpty a ha.
- exact:dense_norm_approximation_filter_laws.
Qed.
End DenseApproximationFilter.
