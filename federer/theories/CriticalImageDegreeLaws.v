(** Federer (1969), 3.4.2(9), p. 316: compare the
    image degrees of the lower-dimensional compact pieces. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealHausdorffMeasure RealHausdorffMeasureLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_real_hausdorff_null_higher_degree]: the
    dimension comparison of 2.10.2 used in 3.4.2(9), p. 316.
    Nullity at a smaller nonnegative real degree implies nullity
    at the larger one. Equal degrees retain the same actual
    measure independently of the proof of nonnegativity. *)
Lemma critical_real_hausdorff_null_higher_degree (R:realType) (X:metricType R)
    (p q:R) (hp:0<=p) (hq:0<=q) (A:set X):
  p<=q ->@real_hausdorff_measure R X p hp A=0%E ->
  @real_hausdorff_measure R X q hq A=0%E.
Proof.
move=>hPQ hNull.
case:(eqVneq p q)=>[hEqual|hDifferent].
- subst q;rewrite (bool_irrelevance hq hp);exact:hNull.
- have hStrict:p<q by rewrite lt_neqAle hDifferent hPQ.
  apply:(@real_hausdorff_finite_higher_degree_zero R X p q hp hq A hStrict).
  by rewrite hNull;exact:ltry.
Qed.

(** Source for [critical_image_degree_dimension_bound]: the
    inequality nu+(gamma-nu)/k<=nu+(mu-nu)/k in the proof
    of 3.4.2(9), p. 316. All divisions have the original
    positive real denominator. *)
Lemma critical_image_degree_dimension_bound (R:realType) (nu gamma mu:nat) (k:R):
  0<k ->(gamma<=mu)%N ->
  nu%:R+(gamma-nu)%:R/k<=nu%:R+(mu-nu)%:R/k.
Proof.
move=>hk hGamma.
have hDifference:((gamma-nu)%:R:R)<=(mu-nu)%:R.
  rewrite ler_nat;exact:(@leq_sub2r nu gamma mu hGamma).
have hInverse:0<=k^-1 by rewrite invr_ge0;exact:ltW hk.
rewrite lerD2l.
have hBound:=ler_wpM2r hInverse hDifference.
exact:hBound.
Qed.

(** Source for [critical_image_degree_above_codimension]: the
    strict inequality nu<tau in the gamma=nu case of
    3.4.2(9), p. 316. It follows from mu>nu and k>0. *)
Lemma critical_image_degree_above_codimension (R:realType) (nu mu:nat) (k:R):
  0<k ->(nu<mu)%N ->nu%:R<nu%:R+(mu-nu)%:R/k.
Proof.
move=>hk hMu;rewrite ltrDl divr_gt0 // ltr0n subn_gt0;exact:hMu.
Qed.
