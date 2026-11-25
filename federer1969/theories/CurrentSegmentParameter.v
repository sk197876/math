(** Federer (1969), 4.1.8, p. 362: the original
    compact parameter interval [0,1] with its scalar
    Lebesgue measure. Reuse the actual relative carrier
    and original subspace measure; no new normalization
    or interval integration theory is introduced. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology normedtype.
From Federer Require Import RealMetricBackground MetricSubsetBackground SubtypeCompactHausdorff
  OpenSubspaceMeasure SubspaceBorelRegularMeasure CompactMetricFiniteRadon
  MeasureUP LebesgueScalarMeasure RadonMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_segment_parameter]: the actual
    scalar interval used in the segment integral of
    Federer 4.1.8, p. 362, with its original relative
    topology and absolute-value metric. *)
Definition current_segment_parameter (R:realType):metricType R:=
  [the metricType R of (metric_subset (`[0,1]:set (real_line_metric R)))].

(** Source for [current_segment_parameter_measure]: the
    original scalar Lebesgue measure restricted to its
    actual parameter interval, supporting Federer 4.1.8,
    p. 362, by 2.5.17, p. 111. *)
Definition current_segment_parameter_measure (R:realType):set (current_segment_parameter R)->\bar R:=
  @open_subspace_measure R (real_line_metric R) `[0,1] (@lebesgue_scalar_measure R).

(** Source for [current_segment_parameter_compact]: the
    original parameter carrier is compact, supporting
    Federer 4.1.8, p. 362, by general topology of
    closed bounded scalar intervals. *)
Lemma current_segment_parameter_compact (R:realType):compact (@setT (current_segment_parameter R)).
Proof. exact:(@set_type_compact_whole (real_line_metric R) `[0,1] (@segment_compact R 0 1)). Qed.

(** Source for [current_segment_parameter_is_measure]:
    restricting the original scalar measure to the actual
    interval gives a measure, supporting Federer 4.1.8,
    p. 362, by 2.1.2, p. 54. *)
Lemma current_segment_parameter_is_measure (R:realType):is_measure (@current_segment_parameter_measure R).
Proof.
exact:(@subspace_image_measure_laws R (real_line_metric R) `[0,1] (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R)).
Qed.

(** Source for [current_segment_parameter_total]: the
    original parameter measure has total mass one,
    supporting Federer 4.1.8, p. 362, by the original
    interval length formula of 2.5.17, p. 111. *)
Lemma current_segment_parameter_total (R:realType):current_segment_parameter_measure (@setT (current_segment_parameter R))= 1%E.
Proof.
rewrite /current_segment_parameter_measure /open_subspace_measure.
have hImage:(set_val @` (@setT (current_segment_parameter R)))=(`[0,1]:set (real_line_metric R)).
  apply/seteqP;split.
  - move=>x [t _ <-];exact:set_valP.
  - move=>t ht;exists (exist _ t (mem_set ht));by [].
by rewrite hImage lebesgue_scalar_segment ?ler01 // subr0.
Qed.

(** Source for [current_segment_parameter_radon]: the
    original scalar parameter measure is Radon on its
    actual compact interval, supporting Federer 4.1.8,
    p. 362. The earlier compact metric criterion
    discharges all measure and regularity conditions. *)
Lemma current_segment_parameter_radon (R:realType):is_radon_measure (@current_segment_parameter_measure R).
Proof.
have hZero:(`[0,1] : set (real_line_metric R)) 0.
  by rewrite /mkset in_itv /= lexx ler01.
pose a:current_segment_parameter R:=exist _ (0:R) (mem_set hZero).
apply:(@compact_metric_finite_borel_radon R (current_segment_parameter R)
  (@current_segment_parameter_measure R) a (@current_segment_parameter_is_measure R)).
- exact:(@subspace_borel_regular_measure R (real_line_metric R) `[0,1] (@lebesgue_scalar_measure R)
    (lebesgue_scalar_is_measure R) (lebesgue_scalar_borel_regular R)).
- exact:current_segment_parameter_compact.
- rewrite current_segment_parameter_total;change (((1:R)%:E< +oo)%E);exact:ltry.
Qed.
