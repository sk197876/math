(** Federer (1969), 1.10.5, p. 48, supporting geometry for the Hilbert-input
    norm equality. The secondary maximum is the length of the tuple sum.
    Quadratic expansions show that an extremal pair must coincide. This
    local proof uses the inner-product laws of 1.7.1 and the parallelogram
    identity; it is not a separately stated claim. Source context and
    context: HilbertBilinearMaximizers.v. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP Bilinear InnerProductUP InnerProductLaws
  InnerNorm InnerParallelogram HilbertBilinearMaximizers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Geometry.
Variable R : rcfType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Local Notation N := (inner_norm hB).

(** Source for [hilbert_sum_sign_maximum]: Federer 1.10.5,
    p. 48, supporting sign choice at a secondary maximum.
    If replacing a pair sum s by -s cannot increase the total
    length, then its inner product with the remaining sum is nonnegative. *)
Lemma hilbert_sum_sign_maximum t s : N (t-s)<=N (t+s) -> 0<=B t s.
Proof.
move=> hh.
have hs := lerXn2r 2 (inner_norm_nonnegative hB _) (inner_norm_nonnegative hB _) hh.
rewrite -subr_ge0 !inner_norm_sqr in hs.
have hb : is_symmetric_bilinear B := conj (inner_bilinear hB) (inner_symmetric hB).
rewrite (symmetric_bilinear_polarization_four hb) pmulr_rge0 in hs; first exact hs.
by rewrite ltr0n.
Qed.

(** Source for [hilbert_scaled_sum_maximum]: Federer 1.10.5,
    p. 48, supporting strict improvement by normalizing a pair.
    For a unit vector z and 0<a<= 2, a secondary maximum that
    permits both sign reversal and replacement of a*z by 2*z forces a= 2. *)
Lemma hilbert_scaled_sum_maximum t z a : N z= 1 -> 0<a -> a<= 2 ->
  N (t-a*:z)<=N (t+a*:z) -> N (t+2*:z)<=N (t+a*:z) -> a= 2.
Proof.
move=> hz ha ha2 hsign hmax.
have hc := hilbert_sum_sign_maximum hsign.
rewrite (bilZr (inner_bilinear hB)) in hc.
change (is_true (0<=a*B t z)) in hc.
rewrite (@pmulr_rge0 R a (B t z) ha) (inner_symmetric hB t z) in hc.
have hs := lerXn2r 2 (inner_norm_nonnegative hB _) (inner_norm_nonnegative hB _) hmax.
rewrite [t+2*:z]addrC [t+a*:z]addrC !inner_norm_sqr
  !(inner_quadratic_expansion hB) in hs.
rewrite -(inner_norm_sqr hB z) hz expr1n !mulr1 lerD2r in hs.
have h2 : (0:R)<= 2 by rewrite ler0n.
have hcross := ler_wpM2r hc (ler_wpM2l h2 ha2).
have hh := le_trans hs (lerD (lexx _) hcross).
rewrite lerD2r in hh.
have h2pos : (0:R)<= 2 by rewrite ler0n.
rewrite (ler_sqr h2pos (ltW ha)) in hh.
apply/eqP; by rewrite eq_le ha2 hh.
Qed.

(** Source for [hilbert_opposite_pair_improves]: Federer
    1.10.5, p. 48, supporting exclusion of opposite entries
    in a secondary maximizing tuple. For a unit z, the two replacements
    t+2z and t-2z cannot both have length at most that of t. *)
Lemma hilbert_opposite_pair_improves t z : N z= 1 ->
  N (t+2*:z)<=N t -> N (t-2*:z)<=N t -> False.
Proof.
move=> hz hp hm.
have hp2 := lerXn2r 2 (inner_norm_nonnegative hB _) (inner_norm_nonnegative hB _) hp.
have hm2 := lerXn2r 2 (inner_norm_nonnegative hB _) (inner_norm_nonnegative hB _) hm.
have hh := lerD hp2 hm2.
have htw : N t^+2+N t^+2= 2*N t^+2 by rewrite mulr_natl mulr2n.
rewrite inner_parallelogram inner_normZ normr_nat hz mulr1 htw in hh.
have h2 : (0:R)<2 by rewrite ltr0n.
rewrite (ler_pM2l h2) -[X in _<=X]addr0 lerD2l in hh.
have hpos : (0:R)<2^+2 := exprn_gt0 2 h2.
have hbad := lt_le_trans hpos hh; by rewrite ltxx in hbad.
Qed.
End Geometry.
