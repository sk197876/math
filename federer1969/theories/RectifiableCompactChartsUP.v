(** Federer (1969), 3.2.18, p. 255:
    independent laws for globally Lipschitz charts
    with compact parameter sets, inverse bounds
    and differentials controlled at every chosen
    point. Existence is proved separately. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  LipschitzUP NormDifferentialUP HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_uniform_compact_rectifiable_chart]:
    the compact K_i, global psi_i and
    three uniform bounds in Federer 3.2.18,
    p. 255. The differential must exist
    at every a in K_i, rather than
    only at almost every such point. *)
Record is_uniform_compact_rectifiable_chart (R : realType) m n (lambda : R)
    (K : set (R_n R m)) (psi : R_n R m -> R_n R n) : Prop := {
  (** Source for [rectifiable_chart_compact]: compact
      parameter domain, Federer 3.2.18, p. 255. *)
  rectifiable_chart_compact : @compact
    (inner_metric_space (@euclidean_inner_productP R m)) K;
  (** Source for [rectifiable_chart_global_bound]: the
      global Lipschitz constant of psi_i is
      at most lambda, Federer 3.2.18, p. 255. *)
  rectifiable_chart_global_bound : @is_metric_lipschitz_bound R
    (inner_metric_space (@euclidean_inner_productP R m))
    (inner_metric_space (@euclidean_inner_productP R n)) setT psi lambda;
  (** Source for [rectifiable_chart_inverse_bound]: the
      inverse Lipschitz inequality on the actual
      image of K_i, Federer 3.2.18, p. 255.
      This also implies injectivity on K_i. *)
  rectifiable_chart_inverse_bound : forall x y, K x -> K y ->
    inner_norm (@euclidean_inner_productP R m) (x-y)<=
      lambda*inner_norm (@euclidean_inner_productP R n) (psi x-psi y);
  (** Source for [rectifiable_chart_differential_bounds]:
      the last display of Federer 3.2.18,
      p. 255. The actual differential
      exists and obeys both norm estimates
      at every point of K_i. *)
  rectifiable_chart_differential_bounds : forall a, K a ->
    exists D : Hom (R_n R m) (R_n R n),
      has_norm_differential (inner_norm (@euclidean_inner_productP R m))
        (inner_norm (@euclidean_inner_productP R n)) setT psi a D /\
      forall v, lambda^-1*inner_norm (@euclidean_inner_productP R m) v<=
        inner_norm (@euclidean_inner_productP R n) (D v) /\
        inner_norm (@euclidean_inner_productP R n) (D v)<=
          lambda*inner_norm (@euclidean_inner_productP R m) v
}.

(** Source for [is_rectifiable_chart_piece]: a
    compact image of a chart contained in
    W, Federer 3.2.18, p. 255.
    No particular parametrization is selected
    in this predicate. *)
Definition is_rectifiable_chart_piece (R : realType) m n (lambda : R)
    (W C : set (R_n R n)) :=
  C `<=` W /\ exists (K : set (R_n R m)) (psi : R_n R m -> R_n R n),
    is_uniform_compact_rectifiable_chart lambda K psi /\ C=psi @` K.

(** Source for [is_rectifiable_compact_chart_cover]:
    the complete disjoint compact-chart conclusion
    of Federer 3.2.18, p. 255.
    Natural index zero corresponds to the
    book's first positive index; empty compact
    slots do not add image points. *)
Definition is_rectifiable_compact_chart_cover (R : realType) m n (lambda : R)
    (W : set (R_n R n)) (K : nat -> set (R_n R m))
    (psi : nat -> R_n R m -> R_n R n) :=
  (forall i, is_uniform_compact_rectifiable_chart lambda (K i) (psi i) /\
    psi i @` K i `<=` W) /\
  (forall i j, i!=j -> forall y, (psi i @` K i) y -> (psi j @` K j) y -> False) /\
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m
    (W `\` (\bigcup_i psi i @` K i))=0%E.
