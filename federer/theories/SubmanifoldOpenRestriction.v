(** Federer (1969), 3.1.19(1), p. 231: restricting a
    submanifold to an ambient open set retains its local
    straightenings. Supporting the local product argument of
    3.2.47, p. 283, on the original translated sphere patch. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness NormMetric EuclideanSubmanifoldUP SubmanifoldStraighteningLocalAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [euclidean_submanifold_open_restriction]:
    locality of the straightening definition, 3.1.19(1),
    p. 231, used on the open sphere patch in
    3.2.47, p. 283. No measurability or closedness
    of the original submanifold is required. *)
Theorem euclidean_submanifold_open_restriction (R:realType) n mu k
    (S U:set (R_n R n)):
  @is_euclidean_submanifold R n mu k S ->
  @open [the topologicalType of real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R n))] U ->
  @is_euclidean_submanifold R n mu k (S `&` U).
Proof.
move=>hS hU a [ha haU].
have [T [C [sigma [tau [Z hChart]]]]]:=hS a ha.
exact (@submanifold_straightening_local_agreement R n mu k
  (S `&` U) S U T C a sigma tau Z hChart hU haU
  (fun x hx=>conj (fun h:S x /\ U x=>proj1 h) (fun h:S x=>conj h hx))).
Qed.
