(** Federer (1969), 3.4.10, p. 337:
    independent laws for the original regular part,
    retaining the original ambient domain and dimension. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness NormMetric AnalyticSubmanifoldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_analytic_regular_locus]: the regular
    part in 3.4.10, p. 337, consists
    exactly of points with a genuine m-dimensional
    analytic manifold neighbourhood in the original domain. *)
Definition is_analytic_regular_locus (R:realType) n m
    (U S L:set (R_n R n)):Prop:=
  forall a,L a <->S a /\exists V:set (R_n R n),
    @open (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) V /\
    V a /\V `<=` U /\@is_euclidean_analytic_submanifold R n m (S `&` V).
