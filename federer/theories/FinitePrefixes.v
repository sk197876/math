(** Federer (1969), 1.7.1, p. 28: the initial spans in Gram-Schmidt's
    assertion. These supporting index and independence lemmas separate the
    finite-prefix bookkeeping from the inner-product argument. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InfiniteSequence FiniteIndependence FiniteSpans.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [family_prefix]: Federer 1.7.1, p. 28,
    the initial sequence u_1,...,u_k of a finite sequence. *)
Definition family_prefix (T : Type) k n (h : (k <= n)%N) (u : 'I_n -> T) (i : 'I_k) :=
  u (widen_ord h i).

(** Source for [family_prefix_refl]: Federer 1.7.1, p. 28,
    a prefix of the full length is the original family. *)
Lemma family_prefix_refl (T : Type) n (h : (n <= n)%N) (u : 'I_n -> T) i :
  family_prefix h u i = u i.
Proof. congr (u _); exact: val_inj. Qed.

(** Source for [family_prefix_compose]: Federer 1.7.1,
    p. 28, taking a prefix of a prefix gives the same initial family. *)
Lemma family_prefix_compose (T : Type) k l n
  (hkl : (k <= l)%N) (hln : (l <= n)%N) (hkn : (k <= n)%N)
  (u : 'I_n -> T) i : family_prefix hkl (family_prefix hln u) i = family_prefix hkn u i.
Proof. congr (u _); exact: val_inj. Qed.

(** Source for [family_prefix_snoc]: Federer 1.7.1,
    p. 28, adjoining the last vector does not change shorter prefixes. *)
Lemma family_prefix_snoc (T : Type) k n (h : (k <= n)%N)
  (h' : (k <= n.+1)%N) (u : 'I_n -> T) v i :
  family_prefix h' (ordinal_snoc u v) i = family_prefix h u i.
Proof.
rewrite /family_prefix.
have hi : widen_ord h' i = widen_ord (leqnSn n) (widen_ord h i) by exact: val_inj.
by rewrite hi ordinal_snoc_before.
Qed.

(** Source for [family_snoc_prefix]: Federer 1.7.1,
    p. 28, a nonempty family is its preceding prefix followed by its last vector. *)
Lemma family_snoc_prefix (T : Type) n (u : 'I_n.+1 -> T) i :
  ordinal_snoc (family_prefix (leqnSn n) u) (u ord_max) i = u i.
Proof.
case: (unliftP ord_max i) => [j ->|->]; last exact: ordinal_snoc_last.
rewrite ordinal_snoc_lift /family_prefix.
congr (u _); apply: val_inj; exact: esym (lift_max j).
Qed.

Section Independence.
Variable K : fieldType.
Variable V : lmodType K.
Variable n : nat.
Variable u : 'I_n.+1 -> V.
Hypothesis hu : finite_independent u.

(** Source for [finite_independent_initial]: Federer
    1.7.1, p. 28, an initial subfamily of an independent sequence
    is independent; here the last vector is removed. *)
Lemma finite_independent_initial : finite_independent (family_prefix (leqnSn n) u).
Proof.
move=> c hc i.
have hs : \sum_j ordinal_snoc c 0 j *: u j = 0.
  under eq_bigr do rewrite -(family_snoc_prefix u).
  rewrite big_ord_recr !ordinal_snoc_last scale0r.
  under eq_bigr do rewrite !ordinal_snoc_before.
  change ((\sum_i c i *: family_prefix (leqnSn n) u i) + 0 = 0).
  by rewrite addr0 hc.
have hh := @hu (ordinal_snoc c 0) hs (widen_ord (leqnSn n) i).
by rewrite ordinal_snoc_before in hh.
Qed.

(** Source for [finite_independent_last_outside]: Federer
    1.7.1, p. 28, the last vector of an independent sequence is
    outside the span of the preceding vectors. *)
Lemma finite_independent_last_outside :
  ~ in_finite_span (family_prefix (leqnSn n) u) (u ord_max).
Proof.
move=> [c hc].
have hs : \sum_j ordinal_snoc c (-1) j *: u j = 0.
  under eq_bigr do rewrite -(family_snoc_prefix u).
  rewrite big_ord_recr !ordinal_snoc_last scaleN1r.
  under eq_bigr do rewrite !ordinal_snoc_before.
  change ((\sum_i c i *: family_prefix (leqnSn n) u i) - u ord_max = 0).
  by rewrite -hc subrr.
have hh := @hu (ordinal_snoc c (-1)) hs ord_max.
rewrite ordinal_snoc_last in hh.
by move: (oner_neq0 K); rewrite -oppr_eq0 hh eqxx.
Qed.
End Independence.
