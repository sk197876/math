(** Federer (1969), 3.2.20, pp. 256–257: scalar
    truncation identities for extended-real weights in the area formula.
    They justify extending the finite-real transformation of 3.2.5(2),
    pp. 244–245, by the increasing-convergence procedure of 2.4.7,
    p. 84. Zero times infinity retains the book's distinguished value. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealPartial.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [finite_nonnegative_weight_minmax]: supporting scalar
    truncation step in Federer 3.2.20, p. 257, applying the
    approximation procedure cited in 3.2.5, p. 245. Multiplication
    by a nonnegative finite weight preserves minima and maxima, including
    weight zero and infinite inputs. *)
Lemma finite_nonnegative_weight_minmax (R : realType) (z t : \bar R) (b : R) :
  (0<=b)%R ->
  (Order.min z t)* b%:E=Order.min (z* b%:E) (t* b%:E) /\
  (Order.max z t)* b%:E=Order.max (z* b%:E) (t* b%:E).
Proof.
move=> hb; have hbE : 0<=b%:E by rewrite lee_fin.
case: (leP z t)=> hzt.
- have hm := lee_wpmul2r hbE hzt.
  split; [by rewrite (min_idPl hm)|by rewrite (max_idPr hm)].
- have hm := lee_wpmul2r hbE (ltW hzt).
  split; [by rewrite (min_idPr hm)|by rewrite (max_idPl hm)].
Qed.

(** Source for [finite_nonnegative_weight_positive_part]: the positive
    part used to reduce the arbitrary signed weight in Federer
    3.2.20, pp. 256–257, to nonnegative truncations. The
    identity includes both infinite signs and the zero-weight case. *)
Lemma finite_nonnegative_weight_positive_part (R : realType) (z : \bar R) (b : R) :
  (0<=b)%R -> extended_positive_part (z* b%:E)=extended_positive_part z* b%:E.
Proof.
move=> hb; have hh := (@finite_nonnegative_weight_minmax R z 0 b hb).2.
rewrite /extended_positive_part mul0e in hh; exact: (esym hh).
Qed.

(** Source for [finite_positive_weight_truncation_exists]: supporting
    real-valued bounded weights for the extended-real area transformation
    in Federer 3.2.20, p. 257. The positive part clipped
    at a finite nonnegative ceiling has an actual finite real value
    between zero and that ceiling, even when the original weight is infinite. *)
Lemma finite_positive_weight_truncation_exists (R : realType) (z : \bar R) (c : R) :
  (0<=c)%R -> exists a : R, (0<=a<=c)%R /\
    a%:E=Order.min (extended_positive_part z) c%:E.
Proof.
move=> hc; pose v := Order.min (extended_positive_part z) c%:E.
have hp : 0<=extended_positive_part z by rewrite /extended_positive_part le_max lexx orbT.
have hcE : 0<=c%:E by rewrite lee_fin.
have hv0 : 0<=v by rewrite /v le_min hp hcE.
have hvc : v<=c%:E by rewrite /v ge_min lexx orbT.
have hvFin : v \is a fin_num.
  rewrite (ge0_fin_numE hv0); exact: (le_lt_trans hvc (ltry c)).
have hEq : (fine v)%:E=v := fineK hvFin.
have ha0 : (0<=fine v)%R by move: hv0; rewrite -hEq lee_fin.
have hac : (fine v<=c)%R by move: hvc; rewrite -hEq lee_fin.
exists (fine v); split; first by apply/andP; split.
exact hEq.
Qed.

(** Source for [finite_weighted_truncation_product]: the clipped-product
    identity used to pass from bounded real weights to arbitrary
    extended-real g in Federer 3.2.20, p. 257. The source
    weighted truncation is the minimum of the positive weighted integrand
    and the finite ceiling times its nonnegative density. *)
Lemma finite_weighted_truncation_product (R : realType) (z : \bar R) (b c a : R) :
  (0<=b)%R -> a%:E=Order.min (extended_positive_part z) c%:E ->
  a%:E* b%:E=Order.min (extended_positive_part (z* b%:E)) (c*b)%R%:E.
Proof.
move=> hb hClip; rewrite hClip (@finite_nonnegative_weight_minmax R (extended_positive_part z) c%:E b hb).1.
by rewrite -EFinM finite_nonnegative_weight_positive_part.
Qed.
