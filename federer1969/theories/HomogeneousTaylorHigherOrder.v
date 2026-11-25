(** Federer (1969), 3.1.24, p. 238: the
    exact Taylor polynomial of each homogeneous coefficient,
    using 1.10.4, p. 46, and 3.1.11, p. 221. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Hom SymmetricForms HomogeneousPolynomialFunctions PolynomialTaylorTerms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [homogeneous_polynomial_taylor_any_higher_order]:
    supporting the differentiated coefficient series in Federer
    3.1.24, p. 238. The exact expansion of a
    homogeneous polynomial of degree m may be extended to
    any order k>=m by the already proved vanishing of
    its higher contractions. Zero polynomials and degree zero
    require no exceptions. *)
Theorem homogeneous_polynomial_taylor_any_higher_order (K:fieldType)
    (h0:[pchar K]=i pred0) (X Y:lmodType K) m (phi:S_m X Y m) k a v :
  (m<=k)%N -> sform_polynomial_value phi (a+v)=
    \sum_(i<k.+1) sform_polynomial_value (symmetric_taylor_term i phi a) v.
Proof.
move=>hk; rewrite (homogeneous_polynomial_taylor h0).
have hn:(m.+1<=k.+1)%N by [].
rewrite (big_ord_widen k.+1
  (fun i=>sform_polynomial_value (symmetric_taylor_term i phi a) v) hn)
  big_mkcond.
apply: eq_bigr=>i _.
case hi:(i<m.+1)%N=>//.
have hmi:(m<i)%N by rewrite leqNgt hi.
rewrite (symmetric_taylor_term_above_degree _ a hmi).
by rewrite (linear0 (@sform_polynomial_value K X Y i)).
Qed.
