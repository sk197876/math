(** Federer (1969), 2.4.17, p. 90: scalar exponent arithmetic for
    logarithmic convexity. These are supporting field-order identities. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [interpolation_fraction_cancel]: Supporting Federer 2.4.17,
    p. 90. *)
Lemma interpolation_fraction_cancel (R : realFieldType) (a u w : R) :
  a != 0 -> w != 0 -> (a/w) * (w/(a * u))=u^-1.
Proof.
move=> ha hw; by rewrite mulrA divfK // invfM mulrA mulfV // div1r.
Qed.

(** Source for [interpolation_fraction_conjugate]: Supporting Federer
    2.4.17, p. 90. *)
Lemma interpolation_fraction_conjugate (R : realFieldType) (x y : R) :
  x+y != 0 -> ((x+y)/x)^-1+((x+y)/y)^-1= 1.
Proof. by move=> h; rewrite !invf_div -mulrDl mulfV. Qed.

(** Source for [positive_weighted_reciprocal_bounds]: Supporting Federer
    2.4.17, p. 90. *)
Lemma positive_weighted_reciprocal_bounds (R : realFieldType) (a b u v : R) :
  0 < a -> 0 < b -> a+b= 1 -> 0 < u -> u <= 1 -> 0 < v -> v <= 1 ->
  0 < a * u+b * v /\ a * u+b * v <= 1.
Proof.
move=> ha hb hab hu hu1 hv hv1; split; first by rewrite addr_gt0 ?mulr_gt0.
have hh := lerD (ler_wpM2l (ltW ha) hu1) (ler_wpM2l (ltW hb) hv1).
by rewrite !mulr1 hab in hh.
Qed.

(** Source for [positive_fraction_sum_ge_one]: Supporting Federer 2.4.17, p.
    90. *)
Lemma positive_fraction_sum_ge_one (R : realFieldType) (x y : R) :
  0 < x -> 0 <= y -> 1 <= (x+y)/x.
Proof. by move=> hx hy; rewrite ler_pdivlMr // mul1r lerDl. Qed.
