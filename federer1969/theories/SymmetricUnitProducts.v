(** Federer (1969), 1.10.5, p. 48: products of unit-ball factors used in the
    finite-dimensional attainment argument. The set is an auxiliary
    parameter image, not a definition of mass. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Bilinear GradedComponents SymmetricAlgebra SymmetricGrading
  SymmetricFormIsomorphism SymmetricTupleScaling SymmetricDecompositions
  SymmetricDecompositionCosts RealNormUP RealNormNormalization.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [symmetric_tuple_component_scalars]: Federer
    1.10.5, p. 48, supporting extraction of all scalar factors
    from a decomposable symmetric vector. *)
Lemma symmetric_tuple_component_scalars (K : fieldType) (V : lmodType K) m
    (v : 'I_m -> V) (c : 'I_m -> K) :
  symmetric_tuple_component [tuple c i *: v i | i<m] =
    (\prod_(i<m) c i) *: symmetric_tuple_component [tuple v i | i<m].
Proof.
apply: val_inj.
change (component_val (symmetric_tuple_component [tuple c i *: v i | i<m]) =
  (\prod_(i<m) c i) *: component_val (symmetric_tuple_component [tuple v i | i<m])).
rewrite !symmetric_tuple_componentE.
change (symmetric_word [seq c i *: v i | i <- enum 'I_m] =
  (\prod_(i<m) c i) *: symmetric_word [seq v i | i <- enum 'I_m]).
by rewrite symmetric_word_scalars big_enum.
Qed.

Section UnitProducts.
Variable R : realFieldType.
Variable V : lmodType R.
Variable N : V -> R.
Hypothesis hN : is_real_norm N.

(** Source for [symmetric_unit_products]: Federer 1.10.5,
    p. 48, auxiliary set of products of m vectors, each of
    norm at most one. Its convex hull will be the mass unit ball. *)
Definition symmetric_unit_products m : set (symmetric_power V m) :=
  fun x => exists t : m.-tuple V,
    (forall v, v \in t -> N v <= 1) /\ x = symmetric_tuple_component t.

(** Source for [symmetric_unit_product_scale]: Federer 1.10.5,
    p. 48, supporting balancedness of the product set. In
    positive degree, a scalar of absolute value at most one can
    be absorbed into the first factor. *)
Lemma symmetric_unit_product_scale m (hm : (0<m)%N) c (hc : `|c|<=1) (x : symmetric_power V m) :
  symmetric_unit_products x -> symmetric_unit_products (c*:x).
Proof.
case: m hm x=> [|m] hm x // [t [ht ->]].
exists (symmetric_scale_first_tuple c t); split; last exact: esym (symmetric_scale_first_component c t).
move=> v; rewrite /symmetric_scale_first_tuple /= in_cons=> /orP [/eqP ->|hv].
- rewrite (real_seminorm_scale (proj1 hN)).
  have hhead : N (thead t)<=1 by apply: ht; rewrite (tuple_eta t) /= in_cons eqxx.
  have hh := ler_wpM2l (normr_ge0 c) hhead; rewrite mulr1 in hh.
  exact: le_trans hh hc.
- apply: ht; rewrite (tuple_eta t) /= in_cons; exact/orP/or_intror.
Qed.

(** Source for [symmetric_unit_products_zero]: Federer 1.10.5,
    p. 48, the product set contains zero in positive degree,
    including when the ambient space is zero-dimensional. *)
Lemma symmetric_unit_products_zero m (hm : (0<m)%N) :
  symmetric_unit_products (0 : symmetric_power V m).
Proof.
have ht : symmetric_unit_products (symmetric_tuple_component [tuple (0:V) | i<m]).
  exists [tuple (0:V) | i<m]; split=> // v /tnthP [i ->].
  by rewrite tnth_mktuple (real_seminorm_zero (proj1 hN)) ler01.
have hh := symmetric_unit_product_scale hm (c:=0) (ltac:(by rewrite normr0 ler01)) ht.
by rewrite scale0r in hh.
Qed.

(** Source for [symmetric_unit_products_negate]: Federer 1.10.5,
    p. 48, the set of positive-degree unit-factor products is
    invariant under negation. *)
Lemma symmetric_unit_products_negate m (hm : (0<m)%N) x :
  symmetric_unit_products (m:=m) x -> symmetric_unit_products (-x).
Proof.
move=> hx.
have hc : `|(-1:R)|<=1 by rewrite normrN normr1.
have hh := @symmetric_unit_product_scale m hm (-1) hc x hx.
by rewrite scaleN1r in hh.
Qed.

(** Source for [symmetric_product_normalized]: Federer 1.10.5,
    p. 48, normalization of a product: it is its product of
    factor lengths times a product of unit-ball vectors. Zero
    factors are included using positive definiteness of the norm. *)
Lemma symmetric_product_normalized m (t : m.-tuple V) :
  exists y, symmetric_unit_products y /\
    symmetric_tuple_component t = symmetric_tuple_cost N t *: y.
Proof.
pose u := [tuple real_norm_normalize N (tnth t i) | i<m].
exists (symmetric_tuple_component u); split.
- exists u; split=> // v /tnthP [i ->].
  rewrite /u tnth_mktuple; exact (@real_norm_normalize_unit R V N (proj1 hN) (tnth t i)).
- have he : t = [tuple N (tnth t i) *: real_norm_normalize N (tnth t i) | i<m].
    apply: eq_from_tnth=> i; rewrite tnth_mktuple.
    symmetry; exact (@real_norm_normalize_reconstruct R V N (proj2 hN) (tnth t i)).
  rewrite {1}he symmetric_tuple_component_scalars; by [].
Qed.
End UnitProducts.
