(** Federer (1969), 4.1.9, pp. 363–364: the
    original current domains have countably finite Radon
    measures, as needed for the preceding 2.6.2 Fubini
    theorem. Reuse the original compact exhaustion of
    4.1.1 and compact finiteness of 2.2.5. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct CurrentDomain SmoothDomainCompactOpenCover
  RadonCompactCoverCountablyMeasurable MeasureUP RadonMeasureUP CountablyMeasurableUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [current_domain_radon_countably_measurable]:
    any Radon measure on the original open Euclidean
    current domain admits a countable cover by finite
    measurable sets, supporting the homotopy integrals in
    Federer 4.1.9, pp. 363–364, through 4.1.1,
    p. 344, and 2.2.5, pp. 62–63. Empty domains
    and dimension zero remain included. *)
Theorem current_domain_radon_countably_measurable (R:realType) n
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (mu:set (current_domain R n U)->\bar R) (hm:is_measure mu) (hr:is_radon_measure mu):
  measure_countably_measurable mu setT.
Proof.
have[C [W [hC [hW [hWC [hCover hWCover]]]]]]:=@smooth_domain_compact_open_cover R (R_n R n)
  (inner_norm (@euclidean_inner_productP R n)) (inner_norm_real_norm (@euclidean_inner_productP R n))
  n (@coordinate_basis R n) (@coordinate_basisP R n) U hU.
exact:(@radon_compact_cover_countably_measurable R (current_domain R n U) mu hm hr C hC hCover).
Qed.
