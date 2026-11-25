(** Federer (1969), 1.10.2, p. 45: supporting calculation for products of
    dual monomial coordinates. This computes the same normalized pairing via
    the divided diagonal of 1.9.4, rather than counting shuffles. *)
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import SymmetricMultiIndices SymmetricExponentBox SymmetricMultiIndexAddition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_box_kronecker]: Federer 1.10.2,
    p. 45, supporting identity: the diagonal coefficient sum for
    exponents alpha,beta has one term exactly when gamma=alpha+beta. *)
Theorem symmetric_box_kronecker (K : fieldType) n (g a b : symmetric_multi_index n) :
  \sum_(c : symmetric_exponent_box g)
    (if symmetric_exponent_box_index g c == a then (1 : K) else 0) *
    (if symmetric_multi_difference g (symmetric_exponent_box_index g c) == b then 1 else 0) =
  if g == symmetric_multi_add a b then 1 else 0.
Proof.
case: eqP=> [->|hne].
- have [c hc] := symmetric_exponent_box_surjective (@symmetric_multi_add_bound n a b).
  rewrite (bigD1 c) //= hc eqxx symmetric_multi_difference_addl eqxx mulr1.
  have hz : (\sum_(d : symmetric_exponent_box (symmetric_multi_add a b) | d != c)
      (if symmetric_exponent_box_index (symmetric_multi_add a b) d == a then (1 : K) else 0) *
      (if symmetric_multi_difference (symmetric_multi_add a b)
        (symmetric_exponent_box_index (symmetric_multi_add a b) d) == b then 1 else 0)) = 0.
    apply: big1=> d hd.
    have hda : symmetric_exponent_box_index (symmetric_multi_add a b) d != a.
      apply/eqP=> he.
      have hdc : d = c := symmetric_exponent_box_injective (eq_trans he (esym hc)).
      by move: hd; rewrite hdc eqxx.
    by rewrite (negbTE hda) mul0r.
  by rewrite hz addr0.
- apply: big1=> c _.
  case: ifP=> [/eqP hc|_]; last by rewrite mul0r.
  case: ifP=> [/eqP hd|_]; last by rewrite mulr0.
  exfalso; apply: hne; symmetry.
  have h := symmetric_multi_add_difference (@symmetric_exponent_box_bound n g c).
  by rewrite hd hc in h.
Qed.
