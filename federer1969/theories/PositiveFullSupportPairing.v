(** Federer (1969), 2.5.7, p. 99: the improving density r has the same
    positive support as g and positive product integral. The full-sign test
    comes from the proved argument for 2.4.16, pp. 89–90; positivity below
    is deduced from the zero-integral test and the positive Lp norm of g. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic PartialExtendedOrderLoci
  MeasureNonnegativeZero SummableRealFunctionUP TotalScalarLpUP TotalScalarLpAlmostEquality
  TotalScalarPairingValue TotalLpPairingBound LpConjugatePair PositivePairingAlmostOrder TotalFullSignLpTest.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [full_support_pairing_strictly_positive]: positivity of
    integral g*r in Federer 2.5.7, p. 99 A zero product integral would force
    g=0 almost everywhere and contradict its positive norm. *)
Lemma full_support_pairing_strictly_positive (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p q (g r : X -> R) :
  is_lp_conjugate_pair p q -> total_scalar_lp mu p g -> total_scalar_lp mu q r ->
  (forall x, (0 <= g x)%R) -> (forall x, (0 <= r x)%R) ->
  (forall x, (0 < g x)%R -> (0 < r x)%R) ->
  0 < total_scalar_lp_norm mu p g -> (0 < total_scalar_pairing mu g r)%R.
Proof.
move=> hpq hg hr hg0 hr0 hsupport hpos.
have hi := (@total_lp_pairing_specification_and_bound R X mu hm p q g r hpq hg hr).1.
have hnonneg := @nonnegative_total_pairing_value R X mu hm g r
  (ex_intro _ (total_scalar_pairing mu g r) hi) hg0 hr0.
rewrite lt_neqAle eq_sym hnonneg andbT; apply/eqP=> hz.
rewrite hz in hi.
have hp : measure_almost_everywhere mu
    (partial_extended_nonnegative_locus (real_total_integrand (fun x => (g x*r x)%R))).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  exists (g x*r x)%:E; split; first by apply/real_total_integrand_graph.
  rewrite lee_fin; exact: mulr_ge0 (hg0 x) (hr0 x).
have heq := @nonnegative_integral_zero_almost_equal R X mu hm _ hi hp.
have hgzero : measure_almost_everywhere mu [set x | g x=0%R].
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ heq)=> x [z [hzprod hz0]].
  have heprod := (proj1 (real_total_integrand_graph _ x z)) hzprod.
  have hez : (0 : \bar R)=z := hz0.
  have hprod : (g x*r x)%R=0%R := EFin_inj (eq_trans heprod (esym hez)).
  case: (eqVneq (g x) 0%R)=> // hgneq.
  have hgpos : (0 < g x)%R by rewrite lt_neqAle eq_sym hgneq hg0.
  have hh := mulr_gt0 hgpos (hsupport x hgpos); by rewrite hprod ltxx in hh.
have hn := @total_scalar_lp_almost_zero_norm R X mu hm p g hg hgzero.
by rewrite hn ltxx in hpos.
Qed.

(** Source for [positive_full_support_dual_witness]: the nonnegative
    full-support r with positive pairing in Federer 2.5.7, p. 99 All three
    conjugate exponent cases, including both endpoints, are covered. The
    later small rescaling preserves the support. *)
Theorem positive_full_support_dual_witness (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p q (g : X -> R) :
  is_lp_conjugate_pair p q -> total_scalar_lp mu p g -> (forall x, (0 <= g x)%R) ->
  0 < total_scalar_lp_norm mu p g ->
  exists r : X -> R, total_scalar_lp mu q r /\ (forall x, (0 <= r x)%R) /\
    (forall x, (0 < r x)%R <-> (0 < g x)%R) /\ (0 < total_scalar_pairing mu g r)%R.
Proof.
move=> hpq hg hg0 hpos.
have [r [hr [_ hsg]]] := @total_full_sign_lp_test_exists R X mu hm q g (lp_conjugate_pair_admissible hpq).2 hg.2.2.2.
have hr0 x : (0 <= r x)%R by rewrite -sgr_ge0 hsg sgr_ge0; exact: hg0.
have hs x : (0 < r x)%R <-> (0 < g x)%R.
  by rewrite -sgr_gt0 hsg sgr_gt0.
exists r; split=> //; split=> //; split=> //.
exact: (@full_support_pairing_strictly_positive R X mu hm p q g r hpq hg hr hg0 hr0
  (fun x hx => (hs x).2 hx) hpos).
Qed.
