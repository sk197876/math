(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    dgpr_blueprint.tex, section 3, lem:classes (cl:product): bilinear
    expressions in maps of polynomial growth have polynomial growth, and
    they have Gaussian decay when the second factor has Gaussian decay;
    the same holds before T on Omega_T.

    The bilinear map is assumed bounded, which is automatic for finite
    dimensional normed spaces (docs/divergences.md). The proof is the
    induction of DgprWeightedBilinear.v with the classes of polynomial and
    Gaussian weights, using the inequality
    (1 + |x|)^c exp(-|x|^2/c') <= c'' exp(-|x|^2/c'') of the blueprint. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets lra.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNorm HilbertFormCompactness ScalarInnerProduct ProductInner
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP
  NormBoundedBilinearUP NormClassHigherBilinear NormRegularity.
From DPGPR Require Import DgprGrowthClasses DgprWeightedBilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section WeightClasses.
Variable R : realType.
Variable X : Type.
Variable r : X->R.
Hypothesis hr : forall x, 0 <= r x.

(** Source for [dgpr_polynomial_class]: the weights
    x |-> c (1 + r(x))^c with 0 < c; proof of lem:classes. *)
Definition dgpr_polynomial_class : (X->R)->Prop :=
  fun w=>exists c, 0 < c /\ w = (fun x=>dgpr_polynomial_weight c (r x)).

(** Source for [dgpr_gaussian_class]: the weights
    x |-> c exp(-r(x)^2/c) with 0 < c; proof of lem:classes. *)
Definition dgpr_gaussian_class : (X->R)->Prop :=
  fun w=>exists c, 0 < c /\ w = (fun x=>dgpr_gaussian_weight c (r x)).

(** Source for [dgpr_polynomial_class_product]: products of polynomial
    weights are dominated by polynomial weights; proof of lem:classes. *)
Lemma dgpr_polynomial_class_product (K0 : X->Prop) (b : R) w1 w2 :
  0 <= b -> dgpr_polynomial_class w1 -> dgpr_polynomial_class w2 ->
  exists w3, dgpr_polynomial_class w3 /\ forall x, K0 x -> b * (w1 x * w2 x) <= w3 x.
Proof.
move=> hb [c1 [h1 ->]] [c2 [h2 ->]].
exists (fun x=>dgpr_polynomial_weight (b * c1 * c2 + c1 + c2) (r x)); split.
- exists (b * c1 * c2 + c1 + c2); split=> //.
  have : 0 <= b * c1 * c2 by apply: mulr_ge0; [apply: mulr_ge0|]; lra.
  lra.
- by move=> x _; exact: dgpr_polynomial_weight_product.
Qed.

(** Source for [dgpr_polynomial_class_sum]: sums of polynomial weights
    are dominated by polynomial weights; proof of lem:classes. *)
Lemma dgpr_polynomial_class_sum (K0 : X->Prop) w w' :
  dgpr_polynomial_class w -> dgpr_polynomial_class w' ->
  exists w'', dgpr_polynomial_class w'' /\ forall x, K0 x -> w x + w' x <= w'' x.
Proof.
move=> [c1 [h1 ->]] [c2 [h2 ->]].
exists (fun x=>dgpr_polynomial_weight (c1 + c2) (r x)); split.
- by exists (c1 + c2); split=> //; lra.
- by move=> x _; exact: dgpr_polynomial_weight_sum.
Qed.

(** Source for [dgpr_polynomial_gaussian_class_product]: a polynomial
    weight times a Gaussian weight is dominated by a Gaussian weight;
    proof of lem:classes. *)
Lemma dgpr_polynomial_gaussian_class_product (K0 : X->Prop) (b : R) w1 w2 :
  0 <= b -> dgpr_polynomial_class w1 -> dgpr_gaussian_class w2 ->
  exists w3, dgpr_gaussian_class w3 /\ forall x, K0 x -> b * (w1 x * w2 x) <= w3 x.
Proof.
move=> hb [c1 [h1 ->]] [c2 [h2 ->]].
exists (fun x=>dgpr_gaussian_weight (dgpr_polynomial_gaussian_constant b c1 c2) (r x)); split.
- exists (dgpr_polynomial_gaussian_constant b c1 c2); split=> //.
  exact: dgpr_polynomial_gaussian_constant_positive.
- by move=> x _; exact: dgpr_polynomial_gaussian_weight_product.
Qed.

(** Source for [dgpr_gaussian_class_sum]: sums of Gaussian weights are
    dominated by Gaussian weights; proof of lem:classes. *)
Lemma dgpr_gaussian_class_sum (K0 : X->Prop) w w' :
  dgpr_gaussian_class w -> dgpr_gaussian_class w' ->
  exists w'', dgpr_gaussian_class w'' /\ forall x, K0 x -> w x + w' x <= w'' x.
Proof.
move=> [c1 [h1 ->]] [c2 [h2 ->]].
exists (fun x=>dgpr_gaussian_weight (c1 + c2) (r x)); split.
- by exists (c1 + c2); split=> //; lra.
- by move=> x _; exact: dgpr_gaussian_weight_sum.
Qed.
End WeightClasses.

Section Product.
Variable R : realType.
Variables (X : lmodType R) (NX : X->R).
Hypothesis hNX : is_real_norm NX.
Variables (Z1 Z2 Z3 : lmodType R) (N1 : Z1->R) (N2 : Z2->R) (N3 : Z3->R).
Hypotheses (h1 : is_real_norm N1) (h2 : is_real_norm N2) (h3 : is_real_norm N3).
Variable beta : Z1->Z2->Z3.
Hypothesis hbeta : norm_bounded_bilinear N1 N2 N3 beta.
Variables (A K0 : set X) (C1 C2 C3 : (X->R)->Prop).
Hypothesis hC12 : forall b w1 w2, 0<=b -> C1 w1 -> C2 w2 ->
  exists w3, C3 w3 /\ forall x, K0 x -> b*(w1 x*w2 x)<=w3 x.
Hypothesis hC3 : forall w w', C3 w -> C3 w' ->
  exists w'', C3 w'' /\ forall x, K0 x -> w x+w' x<=w'' x.

Local Notation ev Y NY hNY := (fun j=>@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY).
Local Notation ZN Y NY hNY := (fun j=>@ContinuousMultilinear.norm R j X Y NX NY hNX hNY).

(** Source for [dgpr_product_weighted_class]: weighted bounds of all
    orders, in the classes C1, C2, C3, for beta(f1,f2) on the open set
    A, with the standard spaces of continuous multilinear maps of
    Federer 3.1.11; proof of lem:classes (cl:product). *)
Lemma dgpr_product_weighted_class (f1 : X->Z1) (f2 : X->Z2) :
  norm_class_all_orders hNX h1 A f1 -> norm_class_all_orders hNX h2 A f2 ->
  (forall j, exists w, C1 w /\ dgpr_derivative_bounded hNX h1 A K0 f1 j w) ->
  (forall j, exists w, C2 w /\ dgpr_derivative_bounded hNX h2 A K0 f2 j w) ->
  norm_class_all_orders hNX h3 A (fun x=>beta (f1 x) (f2 x)) /\
  forall j, exists w, C3 w /\
    dgpr_derivative_bounded hNX h3 A K0 (fun x=>beta (f1 x) (f2 x)) j w.
Proof.
move=> hf1 hf2 hb1 hb2.
have hP j := @ContinuousMultilinear.laws R j X Z1 NX N1 hNX h1.
have hQ j := @ContinuousMultilinear.laws R j X Z2 NX N2 hNX h2.
have hS j := @ContinuousMultilinear.laws R j X Z3 NX N3 hNX h3.
split.
- move=> k; exact: (norm_class_higher_bilinear hNX h1 h2 h3 hP hQ hS hbeta (hf1 k) (hf2 k)).
- move=> k.
  have hw := @dgpr_bilinear_weighted_derivative R X NX hNX A K0 C1 C2 C3 hC12 hC3 k
    Z1 Z2 Z3 N1 N2 N3 h1 h2 h3 _ _ _ _ _ _ _ _ _ hP hQ hS f1 f2 beta hbeta (hf1 k) (hf2 k).
  have [w [hw3 hwb]] := hw (fun i _=>hb1 i) (fun i _=>hb2 i).
  by exists w; split.
Qed.
End Product.

Section Classes.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation TX := ((R^o * R_n R n)%type).
Local Notation BT := (product_inner_productP (scalar_inner_productP R)
  (@euclidean_inner_productP R n)).
Local Notation hNT := (inner_norm_real_norm BT).
Variables (Z1 Z2 Z3 : lmodType R) (N1 : Z1->R) (N2 : Z2->R) (N3 : Z3->R).
Hypotheses (h1 : is_real_norm N1) (h2 : is_real_norm N2) (h3 : is_real_norm N3).
Variable beta : Z1->Z2->Z3.
Hypothesis hbeta : norm_bounded_bilinear N1 N2 N3 beta.

Local Notation rX := (fun x : X=>NX x).
Local Notation rT := (fun p : TX=>NX p.2).

Let hrX : forall x : X, 0 <= rX x.
Proof. by move=> x; exact: inner_norm_nonnegative. Qed.

Let hrT : forall p : TX, 0 <= rT p.
Proof. by move=> p; exact: inner_norm_nonnegative. Qed.

(** Source for [dgpr_classes_product_polynomial]: lem:classes
    (cl:product), blueprint section 3, for maps on R^n: if f1 and f2
    have polynomial growth, then so does beta(f1,f2). *)
Theorem dgpr_classes_product_polynomial (f1 : X->Z1) (f2 : X->Z2) :
  dgpr_polynomial_growth h1 f1 -> dgpr_polynomial_growth h2 f2 ->
  dgpr_polynomial_growth h3 (fun x=>beta (f1 x) (f2 x)).
Proof.
move=> [hf1 hb1] [hf2 hb2].
have hw j : forall (Y : lmodType R) (NY : Y->R) (hNY : is_real_norm NY) (f : X->Y),
    (exists c, 0 < c /\ dgpr_derivative_bounded hNX hNY setT setT f j
      (fun x=>dgpr_polynomial_weight c (NX x))) ->
    exists w, dgpr_polynomial_class rX w /\ dgpr_derivative_bounded hNX hNY setT setT f j w.
  move=> Y NY hNY f [c [hc hb]].
  by exists (fun x=>dgpr_polynomial_weight c (NX x)); split=> //; exists c.
have [hc hb] := @dgpr_product_weighted_class R X NX hNX Z1 Z2 Z3 N1 N2 N3 h1 h2 h3
  beta hbeta setT setT (dgpr_polynomial_class rX) (dgpr_polynomial_class rX)
  (dgpr_polynomial_class rX)
  (fun b w1 w2 hb=>@dgpr_polynomial_class_product R X rX hrX setT b w1 w2 hb)
  (fun w w'=>@dgpr_polynomial_class_sum R X rX hrX setT w w')
  f1 f2 hf1 hf2 (fun j=>hw j _ _ h1 f1 (hb1 j)) (fun j=>hw j _ _ h2 f2 (hb2 j)).
split=> // j; have [w [[c [hc0 ->]] hwb]] := hb j.
by exists c; split.
Qed.

(** Source for [dgpr_classes_product_gaussian]: lem:classes
    (cl:product), blueprint section 3, for maps on R^n: if f1 has
    polynomial growth and f2 has Gaussian decay, then beta(f1,f2) has
    Gaussian decay. Gaussian decay of f2 implies its polynomial growth,
    so the hypothesis of the blueprint on f2 is contained here. *)
Theorem dgpr_classes_product_gaussian (f1 : X->Z1) (f2 : X->Z2) :
  dgpr_polynomial_growth h1 f1 -> dgpr_gaussian_decay h2 f2 ->
  dgpr_gaussian_decay h3 (fun x=>beta (f1 x) (f2 x)).
Proof.
move=> [hf1 hb1] [hf2 hb2].
have hwp j : exists w, dgpr_polynomial_class rX w /\
    dgpr_derivative_bounded hNX h1 setT setT f1 j w.
  have [c [hc hb]] := hb1 j.
  by exists (fun x=>dgpr_polynomial_weight c (NX x)); split=> //; exists c.
have hwg j : exists w, dgpr_gaussian_class rX w /\
    dgpr_derivative_bounded hNX h2 setT setT f2 j w.
  have [c [hc hb]] := hb2 j.
  by exists (fun x=>dgpr_gaussian_weight c (NX x)); split=> //; exists c.
have [hc hb] := @dgpr_product_weighted_class R X NX hNX Z1 Z2 Z3 N1 N2 N3 h1 h2 h3
  beta hbeta setT setT (dgpr_polynomial_class rX) (dgpr_gaussian_class rX)
  (dgpr_gaussian_class rX)
  (fun b w1 w2 hb=>@dgpr_polynomial_gaussian_class_product R X rX hrX setT b w1 w2 hb)
  (fun w w'=>@dgpr_gaussian_class_sum R X rX setT w w')
  f1 f2 hf1 hf2 hwp hwg.
split=> // j; have [w [[c [hc0 ->]] hwb]] := hb j.
by exists c; split.
Qed.

(** Source for [dgpr_classes_product_polynomial_before]: lem:classes
    (cl:product), blueprint section 3: if f1 and f2 have polynomial
    growth before T, then so does beta(f1,f2). *)
Theorem dgpr_classes_product_polynomial_before (T : R) (f1 : TX->Z1) (f2 : TX->Z2) :
  dgpr_polynomial_growth_before h1 T f1 -> dgpr_polynomial_growth_before h2 T f2 ->
  dgpr_polynomial_growth_before h3 T (fun p=>beta (f1 p) (f2 p)).
Proof.
move=> [hf1 hb1] [hf2 hb2].
split; first by move=> k; exact: (norm_class_higher_bilinear hNT h1 h2 h3
  (fun j=>ContinuousMultilinear.laws j hNT h1) (fun j=>ContinuousMultilinear.laws j hNT h2)
  (fun j=>ContinuousMultilinear.laws j hNT h3) hbeta (hf1 k) (hf2 k)).
move=> j a b hbT.
have hwp (f : TX->Z1) : (forall j, exists c, 0 < c /\
    dgpr_derivative_bounded hNT h1 (dgpr_before T) (dgpr_time_strip a b) f j
      (fun p=>dgpr_polynomial_weight c (NX p.2))) ->
    forall j, exists w, dgpr_polynomial_class rT w /\
      dgpr_derivative_bounded hNT h1 (dgpr_before T) (dgpr_time_strip a b) f j w.
  move=> hb i; have [c [hc hbc]] := hb i.
  by exists (fun p=>dgpr_polynomial_weight c (NX p.2)); split=> //; exists c.
have hwq (f : TX->Z2) : (forall j, exists c, 0 < c /\
    dgpr_derivative_bounded hNT h2 (dgpr_before T) (dgpr_time_strip a b) f j
      (fun p=>dgpr_polynomial_weight c (NX p.2))) ->
    forall j, exists w, dgpr_polynomial_class rT w /\
      dgpr_derivative_bounded hNT h2 (dgpr_before T) (dgpr_time_strip a b) f j w.
  move=> hb i; have [c [hc hbc]] := hb i.
  by exists (fun p=>dgpr_polynomial_weight c (NX p.2)); split=> //; exists c.
have [_ hb] := @dgpr_product_weighted_class R TX _ hNT Z1 Z2 Z3 N1 N2 N3 h1 h2 h3
  beta hbeta (dgpr_before T) (dgpr_time_strip a b) (dgpr_polynomial_class rT)
  (dgpr_polynomial_class rT) (dgpr_polynomial_class rT)
  (fun b w1 w2 hb=>@dgpr_polynomial_class_product R TX rT hrT _ b w1 w2 hb)
  (fun w w'=>@dgpr_polynomial_class_sum R TX rT hrT _ w w')
  f1 f2 hf1 hf2 (hwp f1 (fun i=>hb1 i a b hbT)) (hwq f2 (fun i=>hb2 i a b hbT)).
have [w [[c [hc0 ->]] hwb]] := hb j.
by exists c; split.
Qed.

(** Source for [dgpr_classes_product_gaussian_before]: lem:classes
    (cl:product), blueprint section 3: if f1 has polynomial growth
    before T and f2 has Gaussian decay before T, then beta(f1,f2) has
    Gaussian decay before T. *)
Theorem dgpr_classes_product_gaussian_before (T : R) (f1 : TX->Z1) (f2 : TX->Z2) :
  dgpr_polynomial_growth_before h1 T f1 -> dgpr_gaussian_decay_before h2 T f2 ->
  dgpr_gaussian_decay_before h3 T (fun p=>beta (f1 p) (f2 p)).
Proof.
move=> [hf1 hb1] [hf2 hb2].
split; first by move=> k; exact: (norm_class_higher_bilinear hNT h1 h2 h3
  (fun j=>ContinuousMultilinear.laws j hNT h1) (fun j=>ContinuousMultilinear.laws j hNT h2)
  (fun j=>ContinuousMultilinear.laws j hNT h3) hbeta (hf1 k) (hf2 k)).
move=> j a b hbT.
have hwp i : exists w, dgpr_polynomial_class rT w /\
    dgpr_derivative_bounded hNT h1 (dgpr_before T) (dgpr_time_strip a b) f1 i w.
  have [c [hc hbc]] := hb1 i a b hbT.
  by exists (fun p=>dgpr_polynomial_weight c (NX p.2)); split=> //; exists c.
have hwg i : exists w, dgpr_gaussian_class rT w /\
    dgpr_derivative_bounded hNT h2 (dgpr_before T) (dgpr_time_strip a b) f2 i w.
  have [c [hc hbc]] := hb2 i a b hbT.
  by exists (fun p=>dgpr_gaussian_weight c (NX p.2)); split=> //; exists c.
have [_ hb] := @dgpr_product_weighted_class R TX _ hNT Z1 Z2 Z3 N1 N2 N3 h1 h2 h3
  beta hbeta (dgpr_before T) (dgpr_time_strip a b) (dgpr_polynomial_class rT)
  (dgpr_gaussian_class rT) (dgpr_gaussian_class rT)
  (fun b w1 w2 hb=>@dgpr_polynomial_gaussian_class_product R TX rT hrT _ b w1 w2 hb)
  (fun w w'=>@dgpr_gaussian_class_sum R TX rT _ w w')
  f1 f2 hf1 hf2 hwp hwg.
have [w [[c [hc0 ->]] hwb]] := hb j.
by exists c; split.
Qed.

(** Source for [dgpr_classes_product]: lem:classes (cl:product),
    blueprint section 3, as stated there for Omega_T: if f1 and f2 have
    polynomial growth before T, then so does beta(f1,f2); if moreover f2
    has Gaussian decay before T, then so does beta(f1,f2). *)
Theorem dgpr_classes_product (T : R) (f1 : TX->Z1) (f2 : TX->Z2) :
  dgpr_polynomial_growth_before h1 T f1 -> dgpr_polynomial_growth_before h2 T f2 ->
  dgpr_polynomial_growth_before h3 T (fun p=>beta (f1 p) (f2 p)) /\
  (dgpr_gaussian_decay_before h2 T f2 ->
    dgpr_gaussian_decay_before h3 T (fun p=>beta (f1 p) (f2 p))).
Proof.
move=> hf1 hf2; split; first exact: dgpr_classes_product_polynomial_before.
by move=> hg; exact: dgpr_classes_product_gaussian_before.
Qed.
End Classes.
