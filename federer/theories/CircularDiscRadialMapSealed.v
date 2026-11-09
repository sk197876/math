(** Opaque radial maps of the original disc levels,
    Federer (1969), 3.3.19, p. 305. *)
From mathcomp Require Import all_boot finmap reals boolp.
From Federer Require Import EuclideanInnerProduct InnerMetric PartialFunctionUP
  CircularDiscTreeUP CircularDiscRadialMapUP CircularDiscRadialMapExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type CircularDiscRadialMapSignature.
(** Source for [map]: the original eta_n of 3.3.19,
    p. 305, on its exact original level domain. *)
Parameter map:forall (R:realType)
  (H:nat->{fset inner_metric_space (@euclidean_inner_productP R 2)}),
  is_circular_disc_tree H ->nat->
  partial_function (inner_metric_space (@euclidean_inner_productP R 2))
    (inner_metric_space (@euclidean_inner_productP R 2)).
(** Source for [laws]: the independent original domain and
    formula laws of 3.3.19, p. 305. *)
Parameter laws:forall R H hH j,is_circular_disc_radial_map H j (@map R H hH j).
End CircularDiscRadialMapSignature.
Module CircularDiscRadialMap:CircularDiscRadialMapSignature.
(** Source for [map]: hidden existence witness for the
    actual eta_n of 3.3.19, p. 305. *)
Definition map (R:realType)
  (H:nat->{fset inner_metric_space (@euclidean_inner_productP R 2)})
  (hH:is_circular_disc_tree H) j:=
  projT1 (cid (@circular_disc_radial_map_exists R H hH j)).
(** Source for [laws]: the witness satisfies the independently
    specified domain and formula of 3.3.19, p. 305. *)
Lemma laws R H hH j:is_circular_disc_radial_map H j (@map R H hH j).
Proof. exact:(projT2 (cid (@circular_disc_radial_map_exists R H hH j))). Qed.
End CircularDiscRadialMap.
