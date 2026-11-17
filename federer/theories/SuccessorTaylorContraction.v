(** Supporting Federer (1969), 3.4.8(5), p. 328:
    contraction of a successor-degree symmetric form
    in one vector is linear in that vector.
    The proof uses the original contraction formula
    of 1.10.4, p. 46, and multilinearity from
    1.10.1, pp. 43–44. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import Hom AlternatingForms SymmetricForms PolynomialTaylorTerms
  PolynomialTaylorTermContinuity LinearBasis FiniteDualDimension Annihilator.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [successor_taylor_contraction_linear]:
    the single contracted vector occurs linearly in
    the original Taylor coefficient, supporting the
    expanded factorisation proof of 3.4.8(5), p. 328. *)
Lemma successor_taylor_contraction_linear (K:fieldType) (X Y:lmodType K) m
  (F:S_m X Y m.+1) (u:m.-tuple X):
  linear (fun v=>symmetric_taylor_term m F v u).
Proof.
have hSize:size ((val u)++(0:X)::[::])==m.+1.
  by rewrite size_cat size_tuple /= addn1.
have hSmall:(m.+1-m)%N = 1%N by rewrite subSn // subnn.
have hEquation v:symmetric_taylor_term m F v u = F (context_tuple (val u) [::] hSize v).
  rewrite (symmetric_taylor_term_tuple_value (leqnSn m)).
  have hFactor:(((m.+1-m)`!)%:R:K)^-1 = 1 by rewrite hSmall /= invr1.
  rewrite hFactor scale1r.
  congr (F _);apply:val_inj.
  change ((tcast (subnKC (leqnSn m)) [tuple of u++[tuple v | j<m.+1-m]]:seq X)
    = (val u)++[::v]).
  by rewrite val_tcast /= hSmall enum_ordSl enum_ord0 /=.
move=>c x y;rewrite !hEquation.
exact:(@sform_multilinear K X Y m.+1 F (val u) [::] hSize c x y).
Qed.

(** Source for [successor_taylor_contraction_basis_sum]:
    basis expansion reconstructs the contraction in
    the original vector, supporting 3.4.8(5),
    p. 328, from 1.10.4, p. 46. *)
Lemma successor_taylor_contraction_basis_sum (K:fieldType) (X Y:lmodType K) m n
  (F:S_m X Y m.+1) (u:m.-tuple X) (b:'I_n->X) (hb:is_basis b) x:
  \sum_(j<n) dual_basis hb j x*:symmetric_taylor_term m F (b j) u =
    symmetric_taylor_term m F x u.
Proof.
pose L:=@HomMap K X Y (fun v=>symmetric_taylor_term m F v u)
  (introT (asboolP _) (successor_taylor_contraction_linear F u)).
have hCombination:L x = \sum_(j<n) dual_basis hb j x*:(L (b j)).
  rewrite {1}(basis_vector_expansion hb x) linear_sum.
  apply:eq_bigr=>j _;by rewrite linearZ /=.
exact:esym hCombination.
Qed.
