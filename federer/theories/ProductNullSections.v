(** Federer (1969), 2.6.2, p. 117: a product-null set has null measurable
    coordinate sections almost everywhere, and its repeated characteristic
    integral is zero. We derive it directly from covers of arbitrarily small
    cost, using their nonnegative integral majorants; this is a proof
    variation of the printed enclosing-set argument. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic
  MeasureUP MeasureBasic MeasureFiniteClosure MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureConullZeroIntegral NonnegativeSum ProductMeasure
  ProductCoverApproximation ProductSections ProductSectionCoverMajorant VanishingIntegralMajorants.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [product_null_vertical_sections]: direct null-set step in
    Federer 2.6.2, p. 117 No measurability premise on S is needed: its zero
    product measure is sufficient. *)
Theorem product_null_vertical_sections (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (S : set (X * Y)) :
  product_measure ha hb S = 0 ->
  measure_almost_everywhere alpha [set x | beta (product_vertical_section S x) = 0].
Proof.
move=> hz.
have hex n : exists (A : nat -> set X) (B : nat -> set Y),
    (forall m, measure_measurable alpha (A m) /\ measure_measurable beta (B m)) /\
    S `<=` (\bigcup_m (A m `*` B m)) /\
    nonnegative_sum setT (fun m => alpha (A m)*beta (B m)) < (((n.+1)%:R : R)^-1)%:E.
  apply: product_measure_sequence_strict_approximation.
  by rewrite hz lte_fin invr_gt0 ltr0n.
pose A n := projT1 (cid (hex n)).
pose B n := projT1 (cid (projT2 (cid (hex n)))).
have h n := projT2 (cid (projT2 (cid (hex n)))).
have hmaj n := @product_section_cover_integral_majorant R X Y alpha beta ha hb S (A n) (B n)
  (h n).1 (h n).2.1.
pose u n := projT1 (cid (hmaj n)).
have hu n := projT2 (cid (hmaj n)).
apply: (@vanishing_integral_majorants_almost_zero R X alpha ha u
  (fun n => nonnegative_sum setT (fun m => alpha (A n m)*beta (B n m)))
  (fun x => beta (product_vertical_section S x))).
- move=> n x; exact: (hu n).1 x.
- move=> n; exact: (hu n).2.1.
- move=> n; exact: ltW (h n).2.2.
- move=> x; exact: measure_nonnegative.
- move=> n x; exact: (hu n).2.2 x.
Qed.

(** Source for [product_null_vertical_sections_measurable]: direct
    almost-everywhere section measurability for the null case in Federer
    2.6.2(3), pp. 115, 117 *)
Corollary product_null_vertical_sections_measurable (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (S : set (X * Y)) :
  product_measure ha hb S = 0 ->
  measure_almost_everywhere alpha [set x | measure_measurable beta (product_vertical_section S x)].
Proof.
move=> hz; apply: (@measure_almost_everywhere_mono R X alpha ha _ _ _
  (@product_null_vertical_sections R X Y alpha beta ha hb S hz)).
move=> x hx; exact (@measure_null_measurable R Y beta hb (product_vertical_section S x) hx).
Qed.

(** Source for [product_null_vertical_section_integral]: direct zero
    repeated-integral assertion in Federer 2.6.2, p. 117 The outer integral
    of the actual section-measure function exists and equals zero. *)
Corollary product_null_vertical_section_integral (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (S : set (X * Y)) :
  product_measure ha hb S = 0 ->
  is_measure_integral alpha
    (partial_function_total (fun x => beta (product_vertical_section S x))) 0.
Proof.
move=> hz; apply: (measure_almost_zero_integral ha).
exact (@product_null_vertical_sections R X Y alpha beta ha hb S hz).
Qed.
