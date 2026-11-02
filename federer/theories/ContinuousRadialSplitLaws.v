(** Federer (1969), 2.5.20, p. 114: the continuous vector-function space
    satisfies the radial splitting clause of 2.5.12(4), p. 103. This module
    proves the algebraic norm and product identities, including the zero
    vector, before continuity is established separately. Source context:
    CompactFunctionSpaceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_radial_split]: supporting pointwise
    radial formula xi=f/nu(w) times w for the instance of
    2.5.12(4) used in Federer 2.5.20, p. 114.
    Division by zero has value zero and yields xi=0 at w=0. *)
Definition norm_radial_split (R : realType) (E : lmodType R)
    (N : E -> R) (w : E) (f : R) := (f/N w)*:w.

(** Source for [norm_radial_split_norm]: exact norm identity
    nu(xi)=f from Federer 2.5.12(4), p. 103,
    for the continuous-function application of 2.5.20, p. 114. *)
Lemma norm_radial_split_norm (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (w : E) (f : R) :
  0<=f -> f<=N w -> N (norm_radial_split N w f)=f.
Proof.
move=> hf hb; rewrite /norm_radial_split (real_seminorm_scale hN.1).
have hN0 := real_seminorm_nonnegative hN.1 w.
rewrite (ger0_norm (divr_ge0 hf hN0)).
case: (eqVneq (N w) 0)=> [hzero|hne].
- have hf0 : f=0 by apply/eqP; rewrite eq_le hf andbT; by rewrite -hzero.
  by rewrite hzero hf0 mulr0.
- by rewrite divfK.
Qed.

(** Source for [norm_radial_split_product]: the identity
    nu(w) xi=f w from Federer 2.5.12(4), p. 103,
    including the zero-norm boundary needed in 2.5.20, p. 114. *)
Lemma norm_radial_split_product (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (w : E) (f : R) :
  N w*:norm_radial_split N w f=f*:w.
Proof.
rewrite /norm_radial_split scalerA; case: (eqVneq (N w) 0)=> [hz|hn].
- by rewrite (hN.2 w hz) !scaler0.
- by rewrite mulrC divfK.
Qed.
