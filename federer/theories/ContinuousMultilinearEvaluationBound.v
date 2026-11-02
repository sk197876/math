(** Federer (1969), 3.1.11, pp. 219–221:
    evaluation of a continuous multilinear map at
    a fixed tuple is a bounded linear operation.
    This supports contraction of higher differentials
    along the Taylor path. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [continuous_multilinear_evaluation_bounded]:
    the fixed-tuple evaluation bound from the corrected
    operator norm of Federer 3.1.11, p. 219,
    used in the path calculation on p. 221.
    The empty tuple contributes the empty product one. *)
Lemma continuous_multilinear_evaluation_bounded (R : realType) k
    (X Y Z : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (evaluation : {ffun 'I_k->X}->Hom Z Y)
    (ZN : Z->R) (hZ : is_continuous_multilinear_space NX NY evaluation ZN)
    (u : {ffun 'I_k->X}) :
  norm_bounded_linear ZN NY (evaluation u).
Proof.
exists (\prod_(i<k) NX (u i)); split.
- apply: prodr_ge0=>i _; exact (real_seminorm_nonnegative hNX.1 (u i)).
- move=> z; rewrite mulrC.
  exact: multilinear_operator_bound (continuous_multilinear_norm_laws hZ z) u.
Qed.
