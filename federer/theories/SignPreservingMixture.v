(** Federer (1969), 2.4.16, p. 90: retaining the full sign when adding a
    positive full-support test. Source context and weighted-test
    interpretation: DualTestMixture.v. These scalar supporting identities
    justify the pointwise requirement, including zero values, without an
    almost-everywhere relaxation. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [sign_matching_absolute_factor]: supporting
    factorization v=|v| sign(f) for the sign clause of Federer
    2.4.16, pp. 89–90. *)
Lemma sign_matching_absolute_factor (R : realType) (f v : R) :
  Num.sg v=Num.sg f -> v=`|v|*Num.sg f.
Proof. move=> hs; by rewrite -hs mulrC -numEsg. Qed.

(** Source for [positive_sign_mixture]: supporting preservation
    of the exact sign in the positive weighted combination in
    Federer 2.4.16, p. 90. The first term may vanish. *)
Lemma positive_sign_mixture (R : realType) (f u v d : R) :
  0 < d -> d <= 1 -> u=`|u|*Num.sg f -> Num.sg v=Num.sg f ->
  Num.sg ((1-d)*u+d*v)=Num.sg f.
Proof.
move=> hd hd1 hu hv.
have hvf := sign_matching_absolute_factor hv.
have he : (1-d)*u+d*v = ((1-d)*`|u|+d*`|v|)*Num.sg f.
  by rewrite [RHS]mulrDl -!mulrA -hu -hvf.
have [hf|hf] := eqVneq f 0.
- by rewrite he hf sgr0 mulr0 sgr0.
have hvne : v != 0.
  apply/eqP=> hv0; have hs := congr1 (fun r => r==0) hv.
  by move: hs; rewrite hv0 sgr0 eqxx sgr_eq0 (negbTE hf).
have hp : 0 < (1-d)*`|u|+d*`|v|.
  have hleft : 0 <= (1-d)*`|u| by rewrite mulr_ge0 ?normr_ge0 // subr_ge0.
  have hright : 0 < d*`|v| by rewrite mulr_gt0 // normr_gt0.
  exact: (ltr_wpDl hleft hright).
by rewrite he sgrM (gtr0_sg hp) mul1r sgr_id.
Qed.

(** Source for [sign_aligned_product_nonnegative]: supporting nonnegativity
    of the tests in Federer 2.4.16, p. 90, also required. *)
Lemma sign_aligned_product_nonnegative (R : realType) (f u : R) :
  u=`|u|*Num.sg f -> 0 <= f*u.
Proof.
move=> hu; rewrite hu mulrCA [f*Num.sg f]mulrC -normrEsg.
by rewrite mulr_ge0 ?normr_ge0.
Qed.

(** Source for [positive_sign_mixture_product_bound]: retaining
    the first term's contribution in the weighted integral of
    Federer 2.4.16, p. 90, second display. *)
Lemma positive_sign_mixture_product_bound (R : realType) (f u v d : R) :
  0 <= d -> Num.sg v=Num.sg f -> (1-d)*(f*u) <= f*((1-d)*u+d*v).
Proof.
move=> hd hv; rewrite mulrDr !mulrA [f*(1-d)]mulrC [f*d]mulrC -!mulrA lerDl.
apply: mulr_ge0 hd _.
exact: sign_aligned_product_nonnegative (sign_matching_absolute_factor hv).
Qed.
