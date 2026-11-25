(** Federer (1969), 3.2.27, p. 262: a_lambda
    is the actual integral of the coordinate projection's
    fibre count. Specify those integral laws independently
    of their existence and estimates. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric ExteriorIndices
  CoordinateProjection EuclideanLebesgueDimensions PartialFunctionUP PartialFunctionBasic
  ExtendedRealOrderTopology MappingMultiplicity MeasureIntegralUP MeasureIntegralUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_rectifiable_coordinate_masses]: the
    defining display for a_lambda in 3.2.27, p. 262.
    Each finite value satisfies the actual Lebesgue integral
    specification for counting the original W fibre.
    No source replacement or projected-area hypothesis
    is part of this abstract definition. *)
Definition is_rectifiable_coordinate_masses (R:realType) m n
    (W:set (R_n R n)) (a:Lambda n m->R):Prop:=
  forall lambda:Lambda n m,is_measure_integral (@euclidean_lebesgue_measure R m)
    (partial_function_total (fun y=>(@mapping_multiplicity R
      [the choiceType of inner_metric_space (@euclidean_inner_productP R n)]
      [the choiceType of inner_metric_space (@euclidean_inner_productP R m)]
      (@coordinate_projection R n m lambda) W y:extended_real_line R))) (a lambda)%:E.

(** Source for [rectifiable_coordinate_masses_unique]: uniqueness
    of the displayed coordinate integral values in
    3.2.27, p. 262, by the integral laws of
    2.4.2, p. 81. The source need not be
    assumed measurable for uniqueness alone. *)
Lemma rectifiable_coordinate_masses_unique (R:realType) m n
    (W:set (R_n R n)) (a b:Lambda n m->R):
  is_rectifiable_coordinate_masses W a ->is_rectifiable_coordinate_masses W b ->a=b.
Proof.
move=>hA hB; apply:funext=>lambda.
have h:=measure_integral_unique (hA lambda) (hB lambda); by injection h.
Qed.
