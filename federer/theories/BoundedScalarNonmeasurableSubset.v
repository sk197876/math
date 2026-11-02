(** Federer (1969), 3.2.7, p. 246:
    the first example chooses a Lebesgue-nonmeasurable
    subset of [-1,1]. Its existence is supplied by
    the already proved 2.2.4, p. 62. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology normedtype lra.
From Federer Require Import RealMetricBackground RealMetricCompleteness RealLineSeparability
  LebesgueScalarMeasure BernsteinNonmeasurableSubset MeasureUP BorelRegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bounded_scalar_nonmeasurable_subset]: the
    choice of a nonmeasurable subset of [-1,1]
    in the first example of Federer 3.2.7,
    p. 246. Existence follows from 2.2.4,
    not from an additional nonmeasurable-set axiom. *)
Theorem bounded_scalar_nonmeasurable_subset (R:realType):
  exists B:set (real_line_metric R),B `<=` (`[(-1)%R,1%R]:set (real_line_metric R)) /\
    ~measure_measurable (@lebesgue_scalar_measure R) B.
Proof.
have hOrder:(-1:R)<= 1 by lra.
have hMass:lebesgue_scalar_measure (`[(-1)%R,1%R]:set (real_line_metric R))= (2:R)%:E.
  by rewrite lebesgue_scalar_segment //; congr (_%:E); lra.
have hp:(0%E<lebesgue_scalar_measure (`[(-1)%R,1%R]:set (real_line_metric R)))%E.
  by rewrite hMass lte_fin ltr0n.
have hf:(lebesgue_scalar_measure (`[(-1)%R,1%R]:set (real_line_metric R))< +oo)%E.
  rewrite hMass; exact:ltry.
exact (@borel_regular_nonmeasurable_subset R [the metricType R of real_line_metric R]
  (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R) (lebesgue_scalar_borel_regular R)
  `[(-1)%R,1%R] (@real_line_metric_complete R) (@real_line_countable_dense R) hp hf
  (fun x _=>lebesgue_scalar_singleton x)).
Qed.
