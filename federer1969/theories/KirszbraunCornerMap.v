(** Public finite map for Federer (1969), 2.10.44,
    printed p. 202. Only the three original-value
    laws of the opaque witness are exposed. Source
    editions: KirszbraunCornerMapUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import EuclideanInnerProduct InnerMetric PlaneSupremumNorm
  KirszbraunCornerMapUP KirszbraunCornerMapSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [kirszbraun_corner_map]: abstract chosen
    finite-map witness for the printed counterexample
    in 2.10.44, p. 202. *)
Definition kirszbraun_corner_map (R : realType) := @KirszbraunCornerMap.value R.

(** Source for [kirszbraun_corner_map_specification]: proved
    three-value specification of f in 2.10.44,
    p. 202, without exposing any off-source implementation. *)
Lemma kirszbraun_corner_map_specification (R : realType) :
  is_kirszbraun_corner_map (@kirszbraun_corner_map R).
Proof. exact: KirszbraunCornerMap.laws. Qed.
