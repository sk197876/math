(** Federer (1969), 2.4.10, p. 85: upper approximants for the countable
    covering inequality of the density measure. The scan of p. 190 prints a
    sum of restrictions u_{B_i} while the next display uses the integrals of
    u_i; restriction to arbitrary B_i need not preserve measurability. The
    proof here sums the nonnegative measurable approximants themselves.
    Source editions: PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealPartial PartialFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureStepFunctionUP MeasureIntegralUP MeasureIntegralBounds MeasureFiniteUpperApproximant
  MeasureStepIntegralIdentification PartialExtendedOrderLoci MeasureUpperIntegralNonnegative
  MeasureIntegralAlmostEquality MeasureUpperIntegralPositivePart.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_nonnegative_upper_approximation]: supporting
    positive measurable majorant with nearly minimal finite integral for the
    density-measure proof in Federer 2.4.10, p. 85 The target f itself need
    not be measurable. *)
Lemma measure_nonnegative_upper_approximation (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) (e : R) :
  measure_almost_everywhere mu (partial_extended_nonnegative_locus f) ->
  measure_upper_integral mu f < +oo -> (0 < e)%R ->
  exists (v : partial_function X (extended_real_line R)) (b : R),
    (forall x y, partial_function_graph v x y -> 0 <= y) /\
    is_measure_integral mu v b%:E /\
    measure_almost_everywhere mu (partial_extended_le_locus f v) /\
    b%:E < measure_upper_integral mu f + e%:E.
Proof.
move=> hp hfin he.
have hup := @measure_upper_integral_nonnegative R X mu hm f hp.
have hufin : measure_upper_integral mu f \is a fin_num by rewrite (ge0_fin_numE hup).
have hstrict : measure_upper_integral mu f < (fine (measure_upper_integral mu f)+e)%:E.
  rewrite -(fineK hufin) lte_fin ltrDl; exact he.
have [a [[u [hu ha]] hab]] := @measure_upper_value_below R X mu f _ hstrict.
pose w := partial_real_function_embed u.
pose v := partial_extended_function_positive_part w.
have hi : is_measure_integral mu w a := @measure_step_function_integral R X mu hm u a hu.1 ha.
have hgood := @measure_almost_everywhere_and R X mu hm _ _ hp hu.2.
have heq : measure_almost_equal mu w v.
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hgood).
  move=> x [[z [hz hpos]] [r [y [hr [hy hyr]]]]].
  have ezy := partial_function_single_valued hz hy.
  have hrpos : 0 <= r%:E by apply: le_trans _ hyr; by rewrite -ezy.
  have hwr : partial_function_graph w x r%:E by exists r; split.
  exists r%:E; split=> //; exists r%:E; split=> //.
  by rewrite /extended_positive_part max_l.
have hvi := @measure_integral_almost_equal R X mu hm w v a hi heq.
have hvpos : forall x y, partial_function_graph v x y -> 0 <= y.
  move=> x y [z [hz ezy]]; rewrite -ezy; exact: extended_positive_part_nonnegative.
have hfv : measure_almost_everywhere mu (partial_extended_le_locus f v).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hu.2).
  move=> x [r [z [hr [hz hzr]]]]; exists z,(extended_positive_part r%:E); split=> //; split.
  - exists r%:E; split=> //; exists r; by split.
  - apply: le_trans hzr _; by rewrite /extended_positive_part le_max lexx orTb.
have hap : 0 <= a.
  exact (le_trans hup (@measure_upper_integral_bound R X mu f u a hu ha)).
have hafin : a \is a fin_num.
  rewrite (ge0_fin_numE hap); exact: lt_trans hab (ltry _).
exists v,(fine a); split=> //; split; first by rewrite fineK.
split=> //; rewrite fineK // -(fineK hufin) -EFinD; exact hab.
Qed.
