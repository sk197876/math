(** Federer (1969), 2.6.5, p. 120: Borel regularity of Lebesgue products.
    Replace every factor of an approximating rectangle cover by an
    equal-measure Borel hull. The cover cost is unchanged, so Borel
    rectangles suffice in the defining infimum of 2.6.1, pp. 114–115. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import NonnegativeSum MeasureUP BorelRegularMeasureUP TopologicalBorel
  ProductMeasure ProductCoverApproximation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [product_measure_borel_cover_approximation]: Supporting
    Federer 2.6.5, p. 120.Equal-measure Borel factor hulls preserve the
    original cover costs, including zero times infinity. *)
Theorem product_measure_borel_cover_approximation (R : realType) (X Y : topologicalType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta)
    (hra : is_borel_regular_measure alpha) (hrb : is_borel_regular_measure beta)
    (S : set (X * Y)) c :
  product_measure ha hb S < c -> exists (A : nat -> set X) (B : nat -> set Y),
    (forall n, borel_set (A n) /\ borel_set (B n)) /\
    S `<=` (\bigcup_n (A n `*` B n)) /\
    nonnegative_sum setT (fun n => alpha (A n) * beta (B n)) < c.
Proof.
move=> hc; have [A [B [hm [hcover hcost]]]] := @product_measure_sequence_strict_approximation R X Y alpha beta ha hb S c hc.
pose AA n := projT1 (cid (borel_regular_cover hra (A n))).
pose BB n := projT1 (cid (borel_regular_cover hrb (B n))).
have hAA n := projT2 (cid (borel_regular_cover hra (A n))).
have hBB n := projT2 (cid (borel_regular_cover hrb (B n))).
exists AA, BB; split; first by move=> n; split; [exact: (hAA n).2.1|exact: (hBB n).2.1].
split.
- move=> [x y] hs; have [n _ [hx hy]] := hcover (x,y) hs.
  exists n=> //; split; [exact: (hAA n).1 x hx|exact: (hBB n).1 y hy].
- have he : (fun n => alpha (AA n) * beta (BB n)) = (fun n => alpha (A n) * beta (B n)).
    apply: funext=> n; by rewrite -(hAA n).2.2 -(hBB n).2.2.
  by rewrite he.
Qed.
