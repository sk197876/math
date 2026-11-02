(** Federer (1969), 2.5.16, p. 109: when V_a^b g < oo whenever -oo < a < b <
    oo, one considers the nondecreasing function s(x) = V_0^x g and its one
    sided limits s(x-) = sup {s(t) : t < x} and s(x+) = inf {s(t) : t > x},
    with s(x-) <= s(x) <= s(x+). The signed convention V_a^b g = -V_b^a g
    for a > b gives s(u) - s(t) = V_t^u g for t <= u, hence p[g(t), g(u)] <=
    s(u) - s(t). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import ExtendedRealBoundsUP CurveVariationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ArcLength.
Variable R : realType.
Variable Y : metricType R.
Variable g : R -> Y.

(** Source for [curve_locally_finite_variation]: the hypothesis
    V_a^b g < oo whenever -oo < a < b < oo of Federer 2.5.16, p. 109. *)
Definition curve_locally_finite_variation : Prop :=
  forall a b : R, a <= b -> (curve_variation g a b < +oo)%E.

(** Source for [arc_length]: the nondecreasing function s(x) = V_0^x g
    of Federer 2.5.16, p. 109, with the convention V_a^b g = -V_b^a g
    for a > b of the same page. *)
Definition arc_length (x : R) : R :=
  if 0 <= x then fine (curve_variation g 0 x) else - fine (curve_variation g x 0).

(** Source for [arc_length_left_values]: the set {s(t) : t < x} of
    Federer 2.5.16, p. 109. *)
Definition arc_length_left_values (x : R) : set R := arc_length @` [set t | t < x].

(** Source for [arc_length_left]: s(x-) = sup {s(t) : t < x},
    Federer 2.5.16, p. 109. *)
Definition arc_length_left (x : R) : R := sup (arc_length_left_values x).

(** Source for [arc_length_right_values]: the set {-s(t) : t > x}, whose
    supremum is -s(x+), Federer 2.5.16, p. 109. *)
Definition arc_length_right_values (x : R) : set R :=
  (fun t => - arc_length t) @` [set t | x < t].

(** Source for [arc_length_right]: s(x+) = inf {s(t) : t > x},
    Federer 2.5.16, p. 109, written as the negative of a supremum. *)
Definition arc_length_right (x : R) : R := - sup (arc_length_right_values x).

Hypothesis hfin : curve_locally_finite_variation.

(** Source for [curve_variation_fin_num]: supporting finiteness of
    V_a^b g for a <= b under the hypothesis of Federer 2.5.16, p. 109. *)
Lemma curve_variation_fin_num (a b : R) : a <= b -> curve_variation g a b \is a fin_num.
Proof.
move=> hab; rewrite fin_numElt hfin // andbT.
exact: (lt_le_trans (ltNyr 0) (curve_variation_nonnegative g hab)).
Qed.

(** Source for [arc_length_increment]: s(y) - s(x) = V_x^y g for x <= y,
    the additivity V_a^b g + V_b^c g = V_a^c g of Federer 2.5.16, p. 109,
    applied to the three positions of 0. *)
Lemma arc_length_increment (x y : R) :
  x <= y -> (arc_length y - arc_length x)%:E = curve_variation g x y.
Proof.
move=> hxy; rewrite /arc_length; case: ifPn=> h0y; case: ifPn=> h0x.
- rewrite (curve_variation_split g h0x hxy) fineD ?curve_variation_fin_num //.
  by rewrite addrAC subrr add0r fineK ?curve_variation_fin_num.
- have hx0 : x <= 0 by rewrite -ltNge in h0x; exact: ltW.
  by rewrite opprK (curve_variation_split g hx0 h0y) EFinD !fineK ?curve_variation_fin_num // addeC.
- by move: h0y; rewrite (le_trans h0x hxy).
- have hy0 : y <= 0 by rewrite -ltNge in h0y; exact: ltW.
  rewrite (curve_variation_split g hxy hy0) fineD ?curve_variation_fin_num //.
  by rewrite opprK addrCA addNr addr0 fineK ?curve_variation_fin_num.
Qed.

(** Source for [arc_length_monotone]: s is nondecreasing, Federer
    2.5.16, p. 109. *)
Lemma arc_length_monotone (x y : R) : x <= y -> arc_length x <= arc_length y.
Proof.
move=> hxy; rewrite -subr_ge0 -lee_fin arc_length_increment //.
exact: curve_variation_nonnegative.
Qed.

(** Source for [arc_length_distance]: p[g(t), g(u)] <= s(u) - s(t) for
    t <= u, the estimate preceding the one sided limits in Federer
    2.5.16, p. 109. *)
Lemma arc_length_distance (x y : R) :
  x <= y -> mdist (g x) (g y) <= arc_length y - arc_length x.
Proof.
move=> hxy; rewrite -lee_fin arc_length_increment //.
exact: curve_variation_ge_distance.
Qed.

(** Source for [arc_length_zero]: s(0) = V_0^0 g = 0, Federer 2.5.16,
    p. 109. *)
Lemma arc_length_zero : arc_length 0 = 0.
Proof. by rewrite /arc_length lexx curve_variation_self. Qed.

(** Source for [arc_length_left_has_sup]: supporting existence of
    sup {s(t) : t < x}, Federer 2.5.16, p. 109: the set is nonempty and
    bounded by s(x). *)
Lemma arc_length_left_has_sup (x : R) : has_sup (arc_length_left_values x).
Proof.
split; first by exists (arc_length (x - 1)), (x - 1)=> //=; rewrite ltrBlDr ltrDl ltr01.
by exists (arc_length x)=> _ [t /= htx <-]; apply: arc_length_monotone; exact: ltW.
Qed.

(** Source for [arc_length_left_le]: s(x-) <= s(x), Federer 2.5.16,
    p. 109. *)
Lemma arc_length_left_le (x : R) : arc_length_left x <= arc_length x.
Proof.
apply: ge_sup; first exact: (arc_length_left_has_sup x).1.
by move=> _ [t /= htx <-]; apply: arc_length_monotone; exact: ltW.
Qed.

(** Source for [arc_length_le_left]: s(t) <= s(x-) for t < x, Federer
    2.5.16, p. 109. *)
Lemma arc_length_le_left (t x : R) : t < x -> arc_length t <= arc_length_left x.
Proof. by move=> htx; apply: (sup_upper_bound (arc_length_left_has_sup x)); exists t. Qed.

(** Source for [arc_length_left_adherent]: approximation of s(x-) by
    values s(t) with t < x, Federer 2.5.16, p. 109, where
    s(x-) = lim s(t) as t tends to x from the left. *)
Lemma arc_length_left_adherent (x e : R) :
  0 < e -> exists2 t, t < x & arc_length_left x - e < arc_length t.
Proof.
move=> he; have [_ [t /= htx <-] hlt] := sup_adherent he (arc_length_left_has_sup x).
by exists t.
Qed.

(** Source for [arc_length_right_has_sup]: supporting existence of
    inf {s(t) : t > x}, Federer 2.5.16, p. 109: the set of negatives is
    nonempty and bounded by -s(x). *)
Lemma arc_length_right_has_sup (x : R) : has_sup (arc_length_right_values x).
Proof.
split; first by exists (- arc_length (x + 1)), (x + 1)=> //=; rewrite ltrDl ltr01.
by exists (- arc_length x)=> _ [t /= hxt <-]; rewrite lerN2; apply: arc_length_monotone; exact: ltW.
Qed.

(** Source for [arc_length_right_ge]: s(x) <= s(x+), Federer 2.5.16,
    p. 109. *)
Lemma arc_length_right_ge (x : R) : arc_length x <= arc_length_right x.
Proof.
rewrite /arc_length_right lerNr; apply: ge_sup; first exact: (arc_length_right_has_sup x).1.
by move=> _ [t /= hxt <-]; rewrite lerN2; apply: arc_length_monotone; exact: ltW.
Qed.

(** Source for [arc_length_right_le]: s(x+) <= s(t) for t > x, Federer
    2.5.16, p. 109. *)
Lemma arc_length_right_le (x t : R) : x < t -> arc_length_right x <= arc_length t.
Proof.
move=> hxt; rewrite /arc_length_right lerNl.
by apply: (sup_upper_bound (arc_length_right_has_sup x)); exists t.
Qed.

(** Source for [arc_length_right_adherent]: approximation of s(x+) by
    values s(t) with t > x, Federer 2.5.16, p. 109, where
    s(x+) = lim s(t) as t tends to x from the right. *)
Lemma arc_length_right_adherent (x e : R) :
  0 < e -> exists2 t, x < t & arc_length t < arc_length_right x + e.
Proof.
move=> he; have [_ [t /= hxt <-] hlt] := sup_adherent he (arc_length_right_has_sup x).
by exists t=> //; move: hlt; rewrite /arc_length_right ltrNr opprB addrC.
Qed.

(** Source for [arc_length_left_le_right]: s(x-) <= s(x+), Federer
    2.5.16, p. 109. *)
Lemma arc_length_left_le_right (x : R) : arc_length_left x <= arc_length_right x.
Proof. exact: le_trans (arc_length_left_le x) (arc_length_right_ge x). Qed.

End ArcLength.
