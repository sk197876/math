(** Federer (1969), 3.4.8(11), p. 333:
    the zero-dimensional base uses the actual
    point variety. The squared norm gives
    one analytic equation, including dimension zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness SetGermUP FiniteAnalyticVarietyUP AnalyticVarietyGermUP EuclideanSquaredNormAnalytic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_point_analytic_variety]:
    the origin is an actual analytic
    variety in the m=0 proof of
    3.4.8(11), p. 333. *)
Lemma euclidean_point_analytic_variety (R:realType) n:
  @is_finite_analytic_variety R (R_n R n) (inner_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) setT [set 0].
Proof.
split;first exact:openT.
exists (Finite.clone 'I_1 _),(fun (_:'I_1) x=>(inner_norm (@euclidean_inner_productP R n) x)^+2).
split;first by move=>i;exact:euclidean_squared_norm_analytic.
move=>x;split.
- move=>->;split;first exact:Logic.I.
  by move=>_;rewrite inner_norm0 expr0n.
- move=>[_ hZero].
  apply/eqP;rewrite -(@inner_norm_eq0 R (R_n R n) (@euclidean_inner_product R n) (@euclidean_inner_productP R n) x) -sqrf_eq0;apply/eqP;exact:hZero ord0.
Qed.

(** Source for [euclidean_point_analytic_germ]:
    the actual point germ is an
    analytic variety germ, supporting the
    m=0 case of 3.4.8(11), p. 333. *)
Lemma euclidean_point_analytic_germ (R:realType) n:
  @is_analytic_variety_germ R (R_n R n) (inner_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) 0
    (@set_germ (Topological.clone (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0 [set 0]).
Proof.
exists setT,[set 0];split;first exact:Logic.I.
split;[exact:euclidean_point_analytic_variety|reflexivity].
Qed.
