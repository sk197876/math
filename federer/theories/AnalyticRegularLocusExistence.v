(** Federer (1969), 3.4.10, p. 337:
    the regular part exists uniquely by its original
    local manifold condition. This definition assumes no
    stratification or exceptional-set conclusion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness NormMetric AnalyticSubmanifoldUP AnalyticRegularLocusUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [analytic_regular_locus_exists]: existence of
    the set defined in 3.4.10, p. 337,
    retaining all original neighbourhood hypotheses. *)
Theorem analytic_regular_locus_exists (R:realType) n m (U S:set (R_n R n)):
  exists L,is_analytic_regular_locus m U S L.
Proof.
exists [set a|S a /\exists V:set (R_n R n),
    @open (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) V /\
    V a /\V `<=` U /\@is_euclidean_analytic_submanifold R n m (S `&` V)].
by move=>a.
Qed.

(** Source for [analytic_regular_locus_unique]: uniqueness of
    the regular part in 3.4.10, p. 337.
    No chosen chart or defining equation affects it. *)
Theorem analytic_regular_locus_unique (R:realType) n m (U S L M:set (R_n R n)):
  is_analytic_regular_locus m U S L ->
  is_analytic_regular_locus m U S M ->L=M.
Proof.
move=>hL hM;apply/seteqP;split=>a;by rewrite hL hM.
Qed.
