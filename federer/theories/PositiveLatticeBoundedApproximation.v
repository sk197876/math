(** Federer (1969), 2.5.9, p. 100: localize the positive-density argument to
    an order interval for the almost uniqueness assertion. The positive
    density is corrected by erratum p. 2, book p. 100 line 22. Clipping the
    approximant keeps it below the original lattice test, which will supply
    an integrable majorant for arbitrary densities. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP FunctionLatticeUP FunctionLatticeLaws FunctionLatticeRegularityUP
  RealIntegralFunctionalUP TotalScalarLpUP TotalScalarLpLattice TotalScalarLpFiniteSeminorm
  FunctionSeminormDistance RegularLatticeLoneDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_minimum_clipping_error]: supporting clipping
    inequality for the density argument in Federer 2.5.9, p. 100;
    it is not separately numbered in the sources. *)
Lemma real_minimum_clipping_error (R : realType) (h f g : R) :
  (g <= f)%R -> (`|Order.min h f-g| <= `|h-g|)%R.
Proof.
move=> hgf; case: (leP h f)=> hh; first exact: lexx.
rewrite (ger0_norm (_ : (0 <= f-g)%R)); last by rewrite subr_ge0.
rewrite (ger0_norm (_ : (0 <= h-g)%R)); last by rewrite subr_ge0; exact: le_trans hgf (ltW hh).
by rewrite lerD2r; exact: ltW hh.
Qed.

(** Source for [regular_positive_lattice_bounded_approximation]: bounded
    version of the corrected positive-density step in Federer 2.5.9, p. 100
    The approximating function remains in L+. *)
Lemma regular_positive_lattice_bounded_approximation (R : realType) (X : choiceType)
    (L : set (X -> R)) (hL : is_function_lattice L) (F : (X -> R) -> R)
    (mu : set X -> \bar R) (hm : is_measure mu) :
  is_real_integral_functional mu L F -> is_function_lattice_regular L mu ->
  forall f g e, positive_function_lattice L f ->
    positive_function_lattice (total_scalar_lp mu 1) g ->
    (forall x, (g x <= f x)%R) -> (0 < e)%R ->
    exists k, positive_function_lattice L k /\ (forall x, (k x <= f x)%R) /\
      (function_seminorm_distance (finite_total_scalar_lp_norm mu 1) g k < e)%R.
Proof.
move=> hrep hr f g e hf hg hgf he.
have [h [hh hdist]] := @regular_positive_lattice_lone_dense R X L F hL mu hm hrep hr g hg e he.
pose k x := Order.min (h x) (f x).
have hk : positive_function_lattice L k.
  exact: (@function_lattice_minimum R X _ (@positive_function_lattice_laws R X L hL) h f hh hf).
have hhm := @represented_lattice_in_total_lone R X mu hm L F hrep h hh.1.
have hkm := @represented_lattice_in_total_lone R X mu hm L F hrep k hk.1.
have hgk := @total_scalar_lp_subtract R X mu hm 1 g k hg.1 hkm.
have hgh := @total_scalar_lp_subtract R X mu hm 1 g h hg.1 hhm.
exists k; split=> //; split.
- by move=> x; rewrite /k ge_min lexx orbT.
- apply: le_lt_trans _ hdist.
  apply: (@finite_total_scalar_lp_norm_order R X mu hm 1 _ _ hgk hgh)=> x.
  rewrite /k distrC [`|g x-h x|%R]distrC.
  exact: real_minimum_clipping_error (hgf x).
Qed.
