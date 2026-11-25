(** Federer (1969), 3.1.11, p. 223:
    order properties of the sealed flat exponential.
    These give the monotonicity and endpoint
    values of the printed smooth cutoff. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealExponentialUP RealExponentialSealed RealExponentialLaws
  FlatExponentialUP FlatExponentialSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section FlatOrder.
Variable R : realType.
Local Notation f := (@FlatExponential.value R).
Local Notation hf := (@FlatExponential.laws R).

(** Source for [flat_exponential_nonnegative]:
    nonnegativity of the first smooth example
    in Federer 3.1.11, p. 223. *)
Lemma flat_exponential_nonnegative x : 0<=f x.
Proof.
case: (ltP 0 x)=>[hx|hx].
- rewrite (flat_exponential_positive_value hf hx).
  exact: ltW (real_exponential_positive (@RealExponential.laws R) _).
- by rewrite (flat_exponential_nonpositive_value hf hx).
Qed.

(** Source for [flat_exponential_positive]:
    the function in Federer 3.1.11,
    p. 223, is positive exactly on
    the positive half-line. *)
Lemma flat_exponential_positive x : (0<f x)=(0<x).
Proof.
case: (ltP 0 x)=>[hx|hx].
- rewrite (flat_exponential_positive_value hf hx).
  exact: real_exponential_positive (@RealExponential.laws R) _.
- by rewrite (flat_exponential_nonpositive_value hf hx) ltxx.
Qed.

(** Source for [flat_exponential_strictly_increasing_positive]:
    the increasing assertion on the positive
    half-line in Federer 3.1.11, p. 223.
    It follows from reciprocal order and
    the sealed exponential order law. *)
Theorem flat_exponential_strictly_increasing_positive x y :
  0<x -> x<y -> f x<f y.
Proof.
move=> hx hxy; have hy : 0<y := lt_trans hx hxy.
rewrite (flat_exponential_positive_value hf hx)
  (flat_exponential_positive_value hf hy)
  (real_exponential_strict_order (@RealExponential.laws R)) ltrN2.
have hi : y^-1<x^-1 by rewrite ltf_pV2.
have hyi : 0<=y^-1 by rewrite invr_ge0; exact: ltW hy.
by rewrite (ltrXn2r 2 hyi hi).
Qed.

(** Source for [flat_exponential_nondecreasing]:
    the zero extension remains nondecreasing
    on the whole real line, supporting
    the cutoff in Federer 3.1.11, p. 223. *)
Theorem flat_exponential_nondecreasing x y : x<=y -> f x<=f y.
Proof.
move=> hxy; case: (ltP 0 x)=>[hx|hx].
- case: (eqVneq x y)=>[->|hne]; first exact: lexx.
  have hlt : x<y by rewrite lt_neqAle hne hxy.
  exact: ltW (flat_exponential_strictly_increasing_positive hx hlt).
- rewrite (flat_exponential_nonpositive_value hf hx).
  exact: flat_exponential_nonnegative.
Qed.

(** Source for [flat_exponential_unit_bound]:
    the flat exponential is at most one,
    supporting scalar estimates for the cutoff
    in Federer 3.1.11, p. 223. *)
Lemma flat_exponential_unit_bound x : f x<= 1.
Proof.
case: (ltP 0 x)=>[hx|hx].
- rewrite (flat_exponential_positive_value hf hx)
    -(real_exponential_zero (@RealExponential.laws R))
    real_exponential_order oppr_le0.
  exact: sqr_ge0.
- rewrite (flat_exponential_nonpositive_value hf hx); exact: ler01.
Qed.
End FlatOrder.
