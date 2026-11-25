(** Federer (1969), 3.2.18, p. 255: the dimension-zero boundary
    uses the finite-set convention of 3.2.14, p. 252. A point admits
    a compact chart from the sole vector in R^0. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm
  InnerMetric InnerNormInequalities RealNormUP HilbertFormCompactness NormDifferentialUP
  NormDifferentialLinear NormOpenDomainLaws RectifiableCompactChartsUP
  MeasureUP HausdorffMeasure HausdorffCountingMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [zero_dimensional_compact_chart]: supporting dimension-zero
    instance of Federer 3.2.18, p. 255. The constant global map has
    differential zero on the singleton compact domain; both displayed
    differential inequalities are equalities because every source vector
    is zero. Its image has H^0 measure one by 2.10.2(1), p. 171. *)
Lemma zero_dimensional_compact_chart (R : realType) n (lambda : R) (b : R_n R n) :
  0<=lambda ->
  @is_uniform_compact_rectifiable_chart R 0 n lambda [set 0] (fun _=>b) /\
  ((fun _ : R_n R 0=>b) @` [set 0])=[set b] /\
  (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) 0 [set b]= 1)%E.
Proof.
move=> hLam; split; last first.
  split; last exact: hausdorff_zero_singleton.
  apply/seteqP; split; [by move=> y [x _ <-]|move=> y ->; by exists 0].
pose NX := inner_norm (@euclidean_inner_productP R 0).
pose NY := inner_norm (@euclidean_inner_productP R n).
pose hNX := inner_norm_real_norm (@euclidean_inner_productP R 0).
pose hNY := inner_norm_real_norm (@euclidean_inner_productP R n).
constructor.
- exact: compact_set1.
- split=> // x y _ _.
  change (is_true (NY (b-b)<=lambda*NX (x-y))).
  rewrite /NY subrr (inner_norm0 (@euclidean_inner_productP R n)).
  exact: (mulr_ge0 hLam (inner_norm_nonnegative (@euclidean_inner_productP R 0) _)).
- move=> x y -> ->.
  rewrite /NX /NY !subrr !inner_norm0 mulr0; exact: lexx.
- move=> a _; exists (0 : Hom (R_n R 0) (R_n R n)); split.
  + exact: (@norm_differential_constant R (R_n R 0) (R_n R n) NX NY hNX hNY
      setT a b (@norm_full_domain_interior R (R_n R 0) NX a)).
  + move=> v; rewrite (@coordinate_zero R v) hom_zeroE /NX /NY !inner_norm0 !mulr0.
    by split.
Qed.
