(** Federer (1969), 3.1.21, p. 234: normal-bundle
    coordinate changes use the same homogeneous bound for an
    operator and its adjoint, from the pairing law and Cauchy. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  InnerNormInequalities EuclideanAdjoint.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_adjoint_same_bound]: supporting
    continuity of adjoint evaluation in the normal-bundle charts
    of Federer 3.1.21, p. 234, using the adjoint
    and norm laws of 1.7.4–1.7.6, pp. 30–32.
    Every supplied nonnegative operator bound also bounds its adjoint. *)
Lemma euclidean_adjoint_same_bound (R:realType) n
    (L:Hom (R_n R n) (R_n R n)) C : 0<=C ->
  (forall x,inner_norm (@euclidean_inner_productP R n) (L x)<=
    C*inner_norm (@euclidean_inner_productP R n) x) ->
  forall y,inner_norm (@euclidean_inner_productP R n) (@euclidean_adjoint R n L y)<=
    C*inner_norm (@euclidean_inner_productP R n) y.
Proof.
move=>hC hb y.
pose hB:=@euclidean_inner_productP R n.
pose N:=inner_norm hB.
pose z:=@euclidean_adjoint R n L y.
have hz:=inner_norm_nonnegative hB z.
have hy:=inner_norm_nonnegative hB y.
have hs:N z^+2<=C*N z*N y.
  rewrite /N inner_norm_sqr /z euclidean_adjoint_pairing.
  apply: le_trans (inner_cauchy_upper hB (L z) y) _.
  exact (ler_wpM2r hy (hb z)).
change (N z<=C*N y).
case:(eqVneq (N z) 0)=>[->|hn].
- exact: mulr_ge0.
- have hp:0<N z by rewrite lt_def hn hz.
  nra.
Qed.
