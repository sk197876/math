(** Federer (1969), 1.10.5, pp. 47-48: supporting normalization for
    arbitrary normed spaces, rather than only inner-product spaces. Source
    context and comparisons: RealNormUP.v. The auxiliary construction
    supplies proofs of norm estimates; it does not define the norm. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import RealNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Normalization.
Variable R : realFieldType.
Variable V : lmodType R.
Variable N : V -> R.
Hypothesis hN : is_real_seminorm N.

(** Source for [real_norm_normalize]: Federer 1.10.5,
    pp. 47-48, supporting division of a nonzero vector by its norm.
    At seminorm zero the inverse-zero convention gives the zero vector. *)
Definition real_norm_normalize (x : V) := (N x)^-1 *: x.

(** Source for [real_norm_normalize_value]: Federer 1.10.5,
    pp. 47-48, supporting normalization: the new norm is one
    when the original norm is nonzero, and zero otherwise. *)
Lemma real_norm_normalize_value x :
  N (real_norm_normalize x) = if N x == 0 then 0 else 1.
Proof.
rewrite /real_norm_normalize (real_seminorm_scale hN) normfV
  (ger0_norm (real_seminorm_nonnegative hN x)).
case: (eqVneq (N x) 0)=> [hz|hn].
- by rewrite hz invr0 mul0r.
- by rewrite mulVf.
Qed.

(** Source for [real_norm_normalize_unit]: Federer 1.10.5,
    p. 47, supporting admissibility in the unit-tuple supremum. *)
Lemma real_norm_normalize_unit x : N (real_norm_normalize x) <= 1.
Proof. rewrite real_norm_normalize_value; by case: ifP=> _; rewrite ?ler01. Qed.

(** Source for [real_norm_normalize_reconstruct]: Federer 1.10.5,
    pp. 47-48, supporting reconstruction from a normalized vector.
    Positive definiteness is needed when the original norm is zero. *)
Lemma real_norm_normalize_reconstruct (hd : forall x, N x=0 -> x=0) x :
  N x *: real_norm_normalize x = x.
Proof.
rewrite /real_norm_normalize scalerA.
case: (eqVneq (N x) 0)=> [hz|hn].
- rewrite (hd x hz) scaler0; by [].
- by rewrite mulfV // scale1r.
Qed.
End Normalization.
