(** Federer (1969), 2.4.12, p. 87: supporting linear-space laws for
    continuous real functionals. Source context and context:
    ContinuousDualUP.v. Continuity follows from finite norm bounds,
    including zero scalars and zero-dimensional spaces. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ContinuousRealFunctional ContinuousRealFunctionalBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Closure.
Variable R : realType.
Variable V : lmodType R.
Variable N : V -> R.
Hypothesis hN : is_real_norm N.

(** Source for [continuous_hom_zero]: supporting zero element
    of Y*, Federer 2.4.12, p. 87. *)
Lemma continuous_hom_zero :
  is_continuous_real_functional hN (hom_as_linear (0 : Hom V R^o)).
Proof.
apply: (@bounded_real_functional_continuous R V N hN _ 0 (lexx _))=> y.
by rewrite hom_as_linearE hom_zeroE normr0 mul0r.
Qed.

(** Source for [continuous_hom_add]: supporting addition in
    Y*, Federer 2.4.12, p. 87. *)
Lemma continuous_hom_add (a b : Hom V R^o) :
  is_continuous_real_functional hN (hom_as_linear a) ->
  is_continuous_real_functional hN (hom_as_linear b) ->
  is_continuous_real_functional hN (hom_as_linear (a+b)).
Proof.
move=> ha hb.
have [C [hC hCa]] := continuous_real_functional_bound ha.
have [D [hD hDb]] := continuous_real_functional_bound hb.
apply: (@bounded_real_functional_continuous R V N hN _ (C+D));
  first exact: addr_ge0 (ltW hC) (ltW hD).
move=> y; rewrite hom_as_linearE hom_addE.
apply: le_trans (ler_normD _ _) _; rewrite mulrDl.
exact: lerD (hCa y) (hDb y).
Qed.

(** Source for [continuous_hom_scale]: supporting scalar
    multiplication in Y*, Federer 2.4.12, p. 87. *)
Lemma continuous_hom_scale (a : Hom V R^o) c :
  is_continuous_real_functional hN (hom_as_linear a) ->
  is_continuous_real_functional hN (hom_as_linear (c *: a)).
Proof.
move=> ha; have [C [hC hCa]] := continuous_real_functional_bound ha.
apply: (@bounded_real_functional_continuous R V N hN _ (`|c|*C));
  first exact: mulr_ge0 (normr_ge0 c) (ltW hC).
move=> y; rewrite hom_as_linearE hom_scaleE /= normrM -mulrA.
exact: (ler_wpM2l (normr_ge0 c) (hCa y)).
Qed.
End Closure.
