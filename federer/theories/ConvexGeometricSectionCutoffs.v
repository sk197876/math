(** The actual Gillespie section cutoffs in Federer
    (1969), 3.2.45, p. 280. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates ProjectionMeasureUP
  IntegralGeometricGauge IntegralGeometricMeasure IntegralGeometricClosedCovers ExtendedRealOrderTopology ExtendedRealBoundsUP
  MetricScaleEnvelope MetricScaleEnvelopeLaws CaratheodoryReciprocalSupremum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_geometric_section_cutoff]: supporting
    finite-cutoff section integrand in the deduction of
    Federer 3.2.45, p. 280, by 2.10.1,
    p. 170. The existing original closed-convex
    covering infimum is evaluated on the original
    section at cutoff 1/(s+1). This is a
    prescribed expression using the existing sealed
    covering operator, with no new selected object. *)
Definition convex_geometric_section_cutoff (R : realType) m q k (hKQ : (k<=q)%N)
    (A : set (inner_metric_space (@euclidean_inner_productP R (m+q)))) (s : nat)
    (y : inner_metric_space (@euclidean_inner_productP R m)) : extended_real_line R :=
  @metric_scale_envelope R (inner_metric_space (@euclidean_inner_productP R q))
    (closed_convex_euclidean_sets R q) (fun j => val j)
    (fun j => @integral_geometric_gauge R q k hKQ 1 (val j)) (((s.+1)%:R : R)^-1)%R%:E
    [set z | A (@euclidean_block_join R m q (y,z))].

(** Source for [convex_geometric_section_cutoff_nonnegative]: supporting
    nonnegativity in the section limit of Federer
    3.2.45, p. 280, by the original covering
    infimum laws. The original source may be arbitrary. *)
Lemma convex_geometric_section_cutoff_nonnegative (R : realType) m q k (hKQ : (k<=q)%N) A s y :
  0<= @convex_geometric_section_cutoff R m q k hKQ A s y.
Proof.
rewrite /convex_geometric_section_cutoff.
exact: (@metric_scale_envelope_nonnegative R (inner_metric_space (@euclidean_inner_productP R q))
  (closed_convex_euclidean_sets R q) (fun j => val j)
  (fun j => @integral_geometric_gauge R q k hKQ 1 (val j)) _ _
  (metric_scale_envelope_specification _ _ _)).
Qed.

(** Source for [convex_geometric_section_cutoffs_increasing]: supporting
    increasing cutoffs in Federer 3.2.45, p. 280.
    Reuse the proved general covering cutoff order;
    no measurability is asserted for these functions. *)
Lemma convex_geometric_section_cutoffs_increasing (R : realType) m q k (hKQ : (k<=q)%N) A s t :
  (s<=t)%N -> forall y,
  @convex_geometric_section_cutoff R m q k hKQ A s y<=
    @convex_geometric_section_cutoff R m q k hKQ A t y.
Proof.
move=> hST y; rewrite /convex_geometric_section_cutoff.
exact: (@metric_scale_reciprocal_increasing R (inner_metric_space (@euclidean_inner_productP R q))
  (closed_convex_euclidean_sets R q) (fun j => val j)
  (fun j => @integral_geometric_gauge R q k hKQ 1 (val j)) _ s t hST).
Qed.

(** Source for [convex_geometric_section_cutoffs_supremum]: supporting
    recovery of the literal original Gillespie section
    measure in Federer 3.2.45, p. 280. Its
    proved closed-convex covering specification and the
    general cofinal-cutoff theorem identify the supremum.
    Infinite masses and either empty block remain. *)
Theorem convex_geometric_section_cutoffs_supremum (R : realType) m q k (hKQ : (k<=q)%N) A y :
  is_extended_real_supremum
    ((fun s => @convex_geometric_section_cutoff R m q k hKQ A s y) @` setT)
    (@convex_integral_geometric_measure R q k hKQ 1 [set z | A (@euclidean_block_join R m q (y,z))]).
Proof.
rewrite /convex_geometric_section_cutoff.
apply: (@caratheodory_reciprocal_cutoff_supremum R (inner_metric_space (@euclidean_inner_productP R q))
  (closed_convex_euclidean_sets R q) (fun j => val j)
  (fun j => @integral_geometric_gauge R q k hKQ 1 (val j))
  (@convex_integral_geometric_measure R q k hKQ 1)).
exact: convex_integral_geometric_closed_cover_specification (lexx 1).
Qed.
