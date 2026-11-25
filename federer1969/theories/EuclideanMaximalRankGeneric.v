(** Federer (1969), 3.2.33, p. 270: within a
    global analytic rank bound, every point attaining the
    bound is a generic point of 3.1.18, p. 229. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness NormDifferentialUP NormClassOneUP
  LinearRankUP LinearRankAtLeast RankThresholdOpen NormRankZero.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope classical_set_scope.

(** Source for [euclidean_maximal_rank_generic]: the
    openness of the maximal-rank stratum used before the
    corrected 3.1.18 appeal in Federer 3.2.33,
    p. 270. The proved open rank threshold and
    the actual image-basis rank bound give an entire
    constant-rank neighbourhood, with no generic-point
    premise added at the point attaining the bound. *)
Lemma euclidean_maximal_rank_generic (R:realType) m v mu
    (A:set (R_n R m)) (f:R_n R m->R_n R v)
    (D:R_n R m->Hom (R_n R m) (R_n R v)) a:
  is_norm_class_one_field (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R v)) A f D ->
  (forall x,A x ->exists r,has_linear_rank (D x) r /\(r<=mu)%N) ->
  A a ->has_linear_rank (D a) mu ->
  norm_generic_rank (inner_norm (@euclidean_inner_productP R m)) A D a mu.
Proof.
move=>hD hBound ha hRank.
have hThreshold:=@rank_threshold_interior R (R_n R m) (R_n R v)
  (inner_norm (@euclidean_inner_productP R m))
  (@euclidean_inner_product R m) (@euclidean_inner_product R v)
  (@euclidean_inner_productP R m) (@euclidean_inner_productP R v)
  m (@coordinate_basis R m) (@coordinate_basisP R m) erefl A D
  (fun x hx=>(norm_class_one_zero hD hx).1) (norm_class_one_continuity hD) a mu ha
  ((linear_rank_at_leastP mu hRank).2 (leqnn mu)).
have [s [hs hBall]]:=hThreshold.
exists s; split; first exact hs.
move=>h hh; have [hx hAtLeast]:=hBall h hh.
split; first exact hx.
have [r [hr hrBound]]:=hBound (a+h)%R hx.
have hMu:(mu<=r)%N:=(linear_rank_at_leastP mu hr).1 hAtLeast.
have he:r=mu by apply/eqP; rewrite eqn_leq hrBound hMu.
by rewrite -he.
Qed.
