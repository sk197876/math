(** Federer (1969), 2.6.5, p. 120: Borel regularity of finite Lebesgue
    products. We prove the required countable bases and finite-measure
    covers simultaneously by induction, rather than assuming them. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground EuclideanInnerProduct InnerMetric MeasureUP
  BorelRegularMeasureUP CountablyMeasurableUP CountablyMeasurableProduct CountableOpenBaseUP
  ProductCountableBaseSealed ProductMeasure ProductBorelRegularity MeasureCoordinateTransport
  StieltjesBorelRegularity LebesgueScalarMeasure EuclideanCoordinateSplit EuclideanOneCoordinate EuclideanLebesgue.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Local Open Scope classical_set_scope.

(** Source for [positive_euclidean_lebesgue_regularity]: Borel regularity
    asserted in Federer 2.6.5, p. 120, together with the proved countable
    base and countable measurability needed for Fubini and reassociation. *)
Theorem positive_euclidean_lebesgue_regularity (R : realType) n :
  is_borel_regular_measure (@positive_euclidean_lebesgue_measure R n) /\
  measure_countably_measurable (@positive_euclidean_lebesgue_measure R n) setT /\
  exists U : nat -> set (inner_metric_space (@euclidean_inner_productP R n.+1)), is_countable_open_base U.
Proof.
have [V hV] := @real_line_countable_open_base_exists R.
elim: n=> [|n [hr [hc [U hU]]]].
- rewrite positive_euclidean_lebesgue_first; split.
  + exact (@homeomorphic_pushforward_borel_regular R (Topological.clone R _)
      (Topological.clone (inner_metric_space (@euclidean_inner_productP R 1)) _)
      (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R)
      (@euclidean_one_embed R) (@euclidean_one_project R)
      (@euclidean_one_embedK R) (@euclidean_one_projectK R)
      (@euclidean_one_embed_continuous R) (@euclidean_one_project_continuous R)
      (lebesgue_scalar_borel_regular R)).
  + split.
    * exact (@bijective_pushforward_countably_measurable R (Choice.clone R _)
        (Choice.clone (inner_metric_space (@euclidean_inner_productP R 1)) _)
        (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R)
        (@euclidean_one_embed R) (@euclidean_one_project R)
        (@euclidean_one_embedK R) (@euclidean_one_projectK R) (lebesgue_scalar_countably_measurable R)).
    * exists (fun j => (@euclidean_one_project R) @^-1` V j).
      exact (@homeomorphic_countable_open_base (Topological.clone R _)
        (Topological.clone (inner_metric_space (@euclidean_inner_productP R 1)) _)
        (@euclidean_one_embed R) (@euclidean_one_project R) V
        (@euclidean_one_embedK R) (@euclidean_one_projectK R)
        (@euclidean_one_embed_continuous R) (@euclidean_one_project_continuous R) hV).
- rewrite positive_euclidean_lebesgue_successor; split.
  + apply: (@homeomorphic_pushforward_borel_regular R
      (Topological.clone (inner_metric_space (@euclidean_inner_productP R n.+1) * R)%type _)
      (Topological.clone (inner_metric_space (@euclidean_inner_productP R n.+2)) _)
      _ (product_measure_is_measure (positive_euclidean_lebesgue_is_measure R n) (lebesgue_scalar_is_measure R))
      (@euclidean_join R n.+1) (@euclidean_split R n.+1)
      (@euclidean_joinK R n.+1) (@euclidean_splitK R n.+1)
      (@euclidean_join_continuous R n.+1) (@euclidean_split_continuous R n.+1)).
    exact (@product_measure_borel_regular R
      (Topological.clone (inner_metric_space (@euclidean_inner_productP R n.+1)) _)
      (Topological.clone R _) _ _ (positive_euclidean_lebesgue_is_measure R n)
      (lebesgue_scalar_is_measure R) U V hU hV hr (lebesgue_scalar_borel_regular R)).
  + split.
    * apply: (@bijective_pushforward_countably_measurable R
        (Choice.clone (inner_metric_space (@euclidean_inner_productP R n.+1) * R)%type _)
        (Choice.clone (inner_metric_space (@euclidean_inner_productP R n.+2)) _) _
        (product_measure_is_measure (positive_euclidean_lebesgue_is_measure R n) (lebesgue_scalar_is_measure R))
        (@euclidean_join R n.+1) (@euclidean_split R n.+1)
        (@euclidean_joinK R n.+1) (@euclidean_splitK R n.+1)).
      exact: product_whole_countably_measurable hc (lebesgue_scalar_countably_measurable R).
    * exists (fun j => (@euclidean_split R n.+1) @^-1` (ProductCountableBase.value hU hV j)).
      exact (@homeomorphic_countable_open_base
        (Topological.clone (inner_metric_space (@euclidean_inner_productP R n.+1) * R)%type _)
        (Topological.clone (inner_metric_space (@euclidean_inner_productP R n.+2)) _)
        (@euclidean_join R n.+1) (@euclidean_split R n.+1)
        (ProductCountableBase.value hU hV)
        (@euclidean_joinK R n.+1) (@euclidean_splitK R n.+1)
        (@euclidean_join_continuous R n.+1) (@euclidean_split_continuous R n.+1)
        (ProductCountableBase.laws hU hV)).
Qed.
