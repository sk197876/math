(** Federer (1969), 1.8.1, p. 38: the two norm comparisons for comass. That
    formulation includes exterior powers of dimension zero. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm ExteriorCovectorInner
  ComassUP ComassEuclidean AlternatingCoordinates LinearBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory Num.Def.
Local Open Scope ring_scope.

(** Source for [euclidean_le_comass]: Federer 1.8.1, p. 38, the binomial
    norm comparison, written as |phi| <= sqrt(C(n,m)) times comass(phi).
    This avoids the printed inverse constant when C(n,m)=0. *)
Theorem euclidean_le_comass (R : rcfType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) m (hm : (0 < m)%N)
    (phi : A_m V R^o m) c : is_comass h2 hB phi c ->
  exterior_covector_norm h2 hB he phi <= Num.sqrt (('C(n,m))%:R : R) * c.
Proof.
move=> hc; have hh := ler_wsqrtr (@euclidean_squared_le_comass R h2 V B hB n e he m phi c hm hc).
have hn : 0 <= exterior_covector_norm h2 hB he phi := inner_norm_nonnegative _ _.
have hc0 : 0 <= c := comass_nonnegative hm hc.
by rewrite sqrtr_sqr (ger0_norm hn) sqrtrM ?ler0n // sqrtr_sqr (ger0_norm hc0) in hh.
Qed.
