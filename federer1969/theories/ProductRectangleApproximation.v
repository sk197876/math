(** Federer (1969), 2.6.4, pp. 118–119: finite unions of finite-factor
    measurable rectangles approximate every finite-measure measurable set in
    symmetric-difference measure. This expands the printed P0,P1,P2 density
    argument using the actual rectangle-cover infimum of 2.6.1, pp. 114–115.
    Null rectangles with an infinite factor are removed explicitly; no
    ambient countability hypothesis is added. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit NonnegativeSum
  ProductMeasure ProductMeasureSequenceInfimum ProductRectangleMeasurability ProductCoverApproximation
  ProductFiniteFactorCover FiniteUnionMeasureApproximation FiniteCoverMeasureExcess SetSequenceDisjointification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [product_finite_rectangle_approximation]: supporting
    finite-union approximation used for the characteristic-function
    density assertion in Federer 2.6.4, pp. 118–119.
    Every retained factor is measurable with finite measure. *)
Theorem product_finite_rectangle_approximation (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (S : set (X*Y)) (e : R) :
  measure_measurable (product_measure ha hb) S -> product_measure ha hb S < +oo -> (0<e)%R ->
  exists (C : nat -> set X) (D : nat -> set Y) n,
    (forall k, measure_measurable alpha (C k) /\ alpha (C k) < +oo /\
      measure_measurable beta (D k) /\ beta (D k) < +oo) /\
    let U := set_sequence_prefix (fun k => C k `*` D k) n in
    product_measure ha hb ((S `\` U) `|` (U `\` S)) < e%:E.
Proof.
move=> hS hfin he; pose nu := product_measure ha hb.
have hm := product_measure_is_measure ha hb.
pose d : R := (e/2)%R.
have hd : (0<d)%R by rewrite /d divr_gt0 // ltr0n.
have hsf : nu S \is a fin_num by rewrite ge0_fin_numE //; exact (@measure_nonnegative R (Choice.clone (X*Y)%type _) nu hm S).
have hlt : nu S < nu S+d%:E by rewrite -{1}[nu S]adde0 lteD2lE // lte_fin.
have [A [B [hAB [hcover hcost]]]] := @product_measure_sequence_strict_approximation R X Y alpha beta ha hb S _ hlt.
have htop : nu S+d%:E < +oo by apply: lte_add_pinfty=> //; exact: ltry.
have [C [D [N [hCD [hN [hunion hCDcost]]]]]] := @product_finite_factor_cover R X Y alpha beta ha hb A B hAB (lt_trans hcost htop).
pose T := \bigcup_k (A k `*` B k).
pose W := \bigcup_k (C k `*` D k).
have hT : nu T < nu S+d%:E.
  apply: le_lt_trans (@product_measure_sequence_cover_bound R X Y alpha beta ha hb T A B hAB _) hcost.
  by move=> x hx.
have hWsub : W `<=` T by rewrite /T hunion; move=> x hx; left.
have hWfin : nu W < +oo := le_lt_trans (measure_mono hm hWsub) (lt_trans hT htop).
have hexcess := @finite_cover_measure_excess R (Choice.clone (X*Y)%type _) nu hm S T d hS hfin hcover hT.
have hrect k : measure_measurable nu (C k `*` D k).
  exact (@product_measure_rectangle_measurable R X Y alpha beta ha hb (C k) (D k) (hCD k).1 (hCD k).2.2.1).
have [n hn] := @finite_union_measure_approximation R (Choice.clone (X*Y)%type _) nu hm
  (fun k => C k `*` D k) d hrect hWfin hd.
pose U := set_sequence_prefix (fun k => C k `*` D k) n.
have hUW : U `<=` W by move=> x [k _ hx]; exists k.
have hc : (S `\` U) `|` (U `\` S) `<=` N `|` ((W `\` U) `|` (T `\` S)).
  move=> x [[hx hnx]|[hx hnx]].
  - have hxT := hcover x hx; rewrite hunion in hxT.
    case: hxT=> [hxW|hxN]; first by right; left; split.
    by left.
  - right; right; split=> //; exact (hWsub x (hUW x hx)).
have h1 := @measure_binary_cover R (Choice.clone (X*Y)%type _) nu hm _ N ((W `\` U) `|` (T `\` S)) hc.
have h2 := @measure_binary_cover R (Choice.clone (X*Y)%type _) nu hm _ (W `\` U) (T `\` S) (fun _ h => h).
rewrite /nu hN add0e in h1.
exists C,D,n; split; first exact hCD.
apply: le_lt_trans (le_trans h1 h2) _.
have hh := lteD hn hexcess.
have heq : d%:E+d%:E=e%:E by rewrite -EFinD /d -splitr.
by rewrite heq in hh.
Qed.
