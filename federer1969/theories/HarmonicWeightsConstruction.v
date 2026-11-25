(** Private existence witness for the positive vanishing divergent weights
    needed when Federer (1969), 2.4.10, p. 85, invokes the characteristic
    expansion of 2.3.3, p. 76. We choose the harmonic weights 1/(n+1) and
    prove their three laws from finite sums and the Archimedean property.
    This particular witness is infrastructure, not a claim that Federer
    prescribes harmonic weights. The witness stays sealed. Source context:
    PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealOrderLimit ExtendedRealReciprocalBounds
  NonnegativeSum NonnegativeSumNatPrefix NonnegativeSumSupport WeightedCharacteristicExpansionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [harmonic_weight]: private witness of the
    weight hypotheses in 2.3.3, p. 76, used by
    Federer 2.4.10, p. 85. *)
Definition harmonic_weight (R : realType) n := (((n.+1)%:R : R)^-1)%R.
Arguments harmonic_weight {R} n.

(** Source for [harmonic_weight_positive]: positivity of the
    chosen witness supporting Federer 2.4.10, p. 85. *)
Lemma harmonic_weight_positive (R : realType) n : (0 < @harmonic_weight R n)%R.
Proof. by rewrite /harmonic_weight invr_gt0 ltr0n. Qed.

(** Source for [harmonic_weight_decreasing]: supporting monotonicity
    for the zero-limit law of the weights used in Federer
    2.4.10, p. 85. *)
Lemma harmonic_weight_decreasing (R : realType) n m :
  (n <= m)%N -> (@harmonic_weight R m <= harmonic_weight n)%R.
Proof.
move=> hnm.
have hn : (0 < n.+1%:R :> R)%R by rewrite ltr0n.
have hm : (0 < m.+1%:R :> R)%R by rewrite ltr0n.
by rewrite /harmonic_weight (@lef_pV2 R _ _ hm hn) ler_nat.
Qed.

(** Source for [harmonic_weight_zero_limit]: the chosen weights
    satisfy the vanishing hypothesis of 2.3.3, p. 76,
    as used in Federer 2.4.10, p. 85. *)
Lemma harmonic_weight_zero_limit (R : realType) :
  extended_order_limit (fun n => (@harmonic_weight R n)%:E) 0.
Proof.
split.
- move=> a ha; exists 0%N=> n _.
  apply: lt_trans ha _; rewrite lte_fin; exact: harmonic_weight_positive.
- move=> b hb; have [q [hq hqb]] := @extended_rationals_order_dense R 0 b hb.
  have [N hN] := @positive_reciprocal_nat_small R (ratr q) hq.
  exists N=> n hn; apply: lt_trans _ hqb; rewrite lte_fin.
  exact: le_lt_trans (harmonic_weight_decreasing R hn) hN.
Qed.

(** Source for [harmonic_prefix]: private finite sums used
    to establish divergence of the witness for Federer 2.4.10,
    p. 85; numerical summation convention from 2.1.1, p. 52. *)
Definition harmonic_prefix (R : realType) N := (\sum_(i < N) @harmonic_weight R i)%R.
Arguments harmonic_prefix {R} N.

(** Source for [harmonic_doubling_bound]: supporting elementary
    divergence estimate: each doubling block contributes at least
    one half. This proves existence of the weights used in
    Federer 2.4.10, p. 85, without an external series theorem. *)
Lemma harmonic_doubling_bound (R : realType) n :
  (0 < n)%N -> (@harmonic_prefix R n + 2^-1 <= harmonic_prefix (n+n))%R.
Proof.
move=> hn.
have hN : (0 < n%:R :> R)%R by rewrite ltr0n.
have htwo : (0 < 2%:R :> R)%R by rewrite ltr0n.
have ht (i : 'I_n) : ((2*n)%:R^-1 <= @harmonic_weight R (n+i))%R.
  have hden : (0 < (2*n)%:R :> R)%R by rewrite ltr0n muln_gt0.
  have hnum : (0 < (n+i).+1%:R :> R)%R by rewrite ltr0n.
  rewrite /harmonic_weight (@lef_pV2 R _ _ hden hnum) ler_nat.
  rewrite mul2n -addnn -addnS; exact: leq_add (leqnn n) (ltn_ord i).
have hb : (2^-1 <= \sum_(i < n) @harmonic_weight R (n+i))%R.
  have hh : (\sum_(i < n) ((2*n)%:R : R)^-1 <= \sum_(i < n) harmonic_weight (n+i))%R.
    apply: ler_sum=> i _; exact: ht.
  have he : (\sum_(i < n) ((2*n)%:R : R)^-1 = 2^-1)%R.
    by rewrite sumr_const card_ord -[LHS]mulr_natl natrM invfM mulrCA mulfV ?gt_eqF // mulr1.
  by rewrite he in hh.
rewrite /harmonic_prefix big_split_ord /=.
apply: lerD (lexx _) hb.
Qed.

(** Source for [harmonic_power_prefix_bound]: repeated doubling
    gives unbounded finite subsums for the weights used in
    Federer 2.4.10, p. 85. *)
Lemma harmonic_power_prefix_bound (R : realType) k :
  (k%:R / 2 <= @harmonic_prefix R (2^k))%R.
Proof.
elim: k=> [|k ih].
- rewrite mul0r /harmonic_prefix; apply: sumr_ge0=> i _; exact: ltW (harmonic_weight_positive R i).
- have hn : (0 < 2^k)%N by rewrite expn_gt0.
  have hh := @harmonic_doubling_bound R (2^k) hn.
  rewrite expnS mul2n -addnn.
  apply: le_trans _ hh.
  rewrite -addn1 natrD mulrDl mul1r; exact: lerD ih (lexx _).
Qed.

(** Source for [harmonic_prefix_numerical_sum]: supporting
    agreement of finite prefixes and abstract numerical sums,
    used for the weight witness in Federer 2.4.10, p. 85. *)
Lemma harmonic_prefix_numerical_sum (R : realType) N :
  nonnegative_sum [set n | (n < N)%N] (fun n => (@harmonic_weight R n)%:E) = (harmonic_prefix N)%:E.
Proof.
elim: N=> [|N ih].
- by rewrite nonnegative_sum_nat_prefix_zero /harmonic_prefix big_ord0.
- have hp n : 0 <= (@harmonic_weight R n)%:E := ltW (harmonic_weight_positive R n).
  rewrite (nonnegative_sum_nat_prefix_succ N hp) ih /harmonic_prefix big_ord_recr /= EFinD.
  by [].
Qed.

(** Source for [harmonic_weights_diverge]: the chosen weights
    satisfy the divergent-sum premise of 2.3.3, p. 76,
    used by Federer 2.4.10, p. 85. *)
Lemma harmonic_weights_diverge (R : realType) :
  nonnegative_sum setT (fun n => (@harmonic_weight R n)%:E)=+oo.
Proof.
apply: eq_infty=> r.
pose k := Num.bound (2*`|r|)%R.
have hb : (2*`|r| < k%:R)%R.
  apply: archi_boundP; apply: mulr_ge0; [by rewrite ler0n|exact: normr_ge0].
have hrk : (r <= k%:R/2)%R.
  apply: ltW; rewrite ltr_pdivlMr ?ltr0n //.
  apply: le_lt_trans _ hb; rewrite mulrC; apply: ler_wpM2l; first by rewrite ler0n.
  exact: ler_norm.
apply: (le_trans (y:= (harmonic_prefix (2^k))%:E)).
- rewrite lee_fin; exact: le_trans hrk (harmonic_power_prefix_bound R k).
- rewrite -(harmonic_prefix_numerical_sum R (2^k)); apply: nonnegative_sum_subset=> n _; exact I.
Qed.

(** Source for [positive_vanishing_divergent_weights_exist]:
    proved existence of suitable weights for the invocation of
    2.3.3 in Federer 2.4.10, p. 85. *)
Theorem positive_vanishing_divergent_weights_exist (R : realType) :
  exists r : nat -> R, is_positive_vanishing_divergent_sequence r.
Proof.
exists (@harmonic_weight R); constructor.
- exact: harmonic_weight_positive.
- exact: harmonic_weight_zero_limit.
- exact: harmonic_weights_diverge.
Qed.
