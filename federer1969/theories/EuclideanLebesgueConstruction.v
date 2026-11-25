(** Private existence construction of the Euclidean Lebesgue family of
    Federer (1969), 2.6.5, pp. 119–120. Binary product laws are transported
    through the verified coordinate bijections. Source context:
    EuclideanLebesgueUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric MeasureUP MeasurePushforward
  ProductMeasure LebesgueScalarMeasure EuclideanCoordinateSplit EuclideanOneCoordinate EuclideanLebesgueUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section Construction.
Variable R : realType.
Local Notation E k := (inner_metric_space (@euclidean_inner_productP R k)).

(** Source for [euclidean_lebesgue_witness]: private
    recursive witness for the finite-product definition in
    Federer 2.6.5, pp. 119–120, on the actual
    Euclidean carriers. Each stage includes its measure proof. *)
Fixpoint euclidean_lebesgue_witness n : {mu : set (E n.+1) -> \bar R | is_measure mu} :=
  match n as k return {mu : set (E k.+1) -> \bar R | is_measure mu} with
  | 0 => exist _ (measure_pushforward (@euclidean_one_embed R) (@lebesgue_scalar_measure R))
      (measure_pushforward_is_measure (@euclidean_one_embed R) (lebesgue_scalar_is_measure R))
  | k.+1 => exist _
      (measure_pushforward (@euclidean_join R k.+1)
        (product_measure (proj2_sig (euclidean_lebesgue_witness k)) (lebesgue_scalar_is_measure R)))
      (measure_pushforward_is_measure (@euclidean_join R k.+1)
        (product_measure_is_measure (proj2_sig (euclidean_lebesgue_witness k)) (lebesgue_scalar_is_measure R)))
  end.

(** Source for [euclidean_lebesgue_family_exists]: existence
    for the abstract Euclidean product laws in Federer
    2.6.5, pp. 119–120. Only the laws are exposed
    by the subsequent opaque module. *)
Theorem euclidean_lebesgue_family_exists :
  exists nu : forall n, set (E n.+1) -> \bar R, is_euclidean_lebesgue_family nu.
Proof.
exists (fun n => proj1_sig (euclidean_lebesgue_witness n)); constructor.
- move=> n; exact: proj2_sig (euclidean_lebesgue_witness n).
- by [].
- move=> n.
  have he : measure_pushforward (@euclidean_split R n.+1)
      (proj1_sig (euclidean_lebesgue_witness n.+1)) =
      product_measure (proj2_sig (euclidean_lebesgue_witness n)) (lebesgue_scalar_is_measure R).
    apply: funext=> A.
    change (product_measure (proj2_sig (euclidean_lebesgue_witness n)) (lebesgue_scalar_is_measure R)
      ((@euclidean_join R n.+1) @^-1` ((@euclidean_split R n.+1) @^-1` A)) =
      product_measure (proj2_sig (euclidean_lebesgue_witness n)) (lebesgue_scalar_is_measure R) A).
    have hpre : (@euclidean_join R n.+1) @^-1` ((@euclidean_split R n.+1) @^-1` A) = A.
      by apply/seteqP; split=> p /=; rewrite euclidean_joinK.
    by rewrite hpre.
  rewrite he; exact: product_measure_specification.
Qed.
End Construction.
