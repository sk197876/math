(** Federer (1969), 2.2.15, pp. 70–71: every real-valued Borel function on a
    metric space is Baire. Combine the abstract integer-cell approximants,
    their printed countable characteristic-sum representation, and their
    reciprocal error bound. *)
From mathcomp Require Import all_boot classical_sets reals topology.
From Federer Require Import RealMetricBackground BorelFunctionUP BaireFunctions BaireBorel
  RealQuantisationSealed RealQuantisationBounds RealQuantisationBaire.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [real_borel_function_baire]: direct real-
    valued converse in Federer 2.2.15, pp. 70–71.
    Each h_i is Baire and h_i converges pointwise to f.
    The source metric space need not be complete or separable,
    and f need not be bounded. *)
Theorem real_borel_function_baire (R : realType) (X : metricType R)
    (f : X -> real_line_metric R) : is_borel_function f -> is_baire_function f.
Proof.
move=> hf.
pose q k := @RealQuantisation.value R X f k.
have hq k := @RealQuantisation.laws R X f k.
apply: (@baire_function_pointwise_limit R X [the metricType R of real_line_metric R] q f).
- move=> k; exact: borel_real_quantisation_baire hf (hq k).
- exact: real_quantisations_pointwise_limit hq.
Qed.

(** Source for [real_borel_iff_baire]: equivalence combining
    both inclusions in Federer 2.2.15, pp. 70–71,
    for real-valued maps on arbitrary metric sources. *)
Theorem real_borel_iff_baire (R : realType) (X : metricType R)
    (f : X -> real_line_metric R) : is_borel_function f <-> is_baire_function f.
Proof. split; [exact: real_borel_function_baire|exact: baire_function_borel]. Qed.
