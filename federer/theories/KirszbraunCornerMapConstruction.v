(** Private finite-map witness for Federer (1969),
    2.10.44, printed p. 202. A piecewise map
    satisfies the three original value laws because
    the printed source points are distinct. Later
    arguments use only the opaque laws. Source
    editions: KirszbraunCorners.v and KirszbraunCornerMapUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import EuclideanInnerProduct InnerMetric PlaneSupremumNorm
  KirszbraunCorners KirszbraunCornerMapUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [kirszbraun_corner_map_exists]: direct
    existence of the three-value map printed in
    2.10.44, p. 202. Arbitrary values off
    the original source are only private witness data. *)
Lemma kirszbraun_corner_map_exists (R : realType) :
  exists f : plane_supremum_metric R -> inner_metric_space (@euclidean_inner_productP R 2),
    is_kirszbraun_corner_map f.
Proof.
have [hBA [hCA hCB]] := kirszbraun_corners_distinct R.
exists (fun x=>if x==kirszbraun_corner_first R then kirszbraun_equilateral_first R else
  if x==kirszbraun_corner_second R then kirszbraun_equilateral_second R else kirszbraun_equilateral_third R).
constructor.
- by rewrite eqxx.
- by rewrite (negbTE hBA) eqxx.
- by rewrite (negbTE hCA) (negbTE hCB).
Qed.
