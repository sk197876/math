(** Federer (1969), 2.4.3(7), p. 82: the lower integral is at most the upper
    integral. Following the printed proof, a strict reverse inequality would
    give a negative upper integral of f-f, contradicting nonnegativity.
    Source context: PartialExtendedOrderLoci.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealPartial PartialFunctionUP PartialFunctionPostcomposition
  PartialExtendedArithmetic MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralBounds
  PartialExtendedOrderLoci MeasureIntegralNegation MeasureUpperIntegralSubadditive MeasureUpperIntegralNonnegative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [strict_extended_difference_negative]: supporting
    arithmetic step in the proof of Federer 2.4.3(7), p. 82:
    a strict inequality makes subtraction defined and negative. *)
Lemma strict_extended_difference_negative (R : realType) (a b : \bar R) :
  a < b -> extended_add a (-b) = Some (a-b) /\ a-b < 0.
Proof.
case: a=> [a| |]; case: b=> [b| |] //= hab; split;
  rewrite /extended_add /adde_def /= ?eqxx //;
  by rewrite ?lte_fin ?subr_lt0 ?ltNyr.
Qed.

(** Source for [defined_self_difference_nonnegative]: supporting
    domain-sensitive form of f-f>=0 for Federer 2.4.3(7),
    p. 82. Differences of equal infinities remain undefined. *)
Lemma defined_self_difference_nonnegative (R : realType) (a z : \bar R) :
  extended_add a (-a) = Some z -> 0 <= z.
Proof.
case: a=> [a| |]; rewrite /extended_add /adde_def /= ?eqxx //.
move=> [<-]; by rewrite -EFinD subrr.
Qed.

(** Source for [measure_lower_integral_le_upper]: direct
    Federer 2.4.3(7), p. 82, preserving the book's proof
    by negation, subadditivity and nonnegativity. It holds for
    arbitrary partial f: if its domain is not conull there are
    no upper or lower step functions, giving the trivial bounds. *)
Theorem measure_lower_integral_le_upper (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) :
  measure_lower_integral mu f <= measure_upper_integral mu f.
Proof.
rewrite leNgt; apply/negP=> hbad.
have [hd hneg] := strict_extended_difference_negative hbad.
have he := @measure_lower_integral_negation R X mu hm f.
rewrite he oppeK in hd hneg.
have hfin : measure_upper_integral mu f +
    measure_upper_integral mu (partial_extended_function_negate f) < +oo.
  exact: lt_trans hneg (ltry 0%R).
have [hdom hle] := @measure_upper_integral_sum_consequences R X mu hm f
  (partial_extended_function_negate f) _ hd hfin.
have hpos : measure_almost_everywhere mu (partial_extended_nonnegative_locus
    (partial_extended_function_add f (partial_extended_function_negate f))).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hdom).
  move=> x [z hz]; exists z; split=> //.
  have [a [b [ha [[a' [ha' he']] hab]]]] := (partial_extended_function_add_graph _ _ _ _).1 hz.
  have haa := partial_function_single_valued ha ha'.
  rewrite -haa in he'; rewrite -he' in hab.
  exact: defined_self_difference_nonnegative hab.
have hn := @measure_upper_integral_nonnegative R X mu hm _ hpos.
have hh := le_lt_trans hn (le_lt_trans hle hneg).
by move: hh; rewrite ltxx.
Qed.
