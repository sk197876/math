(** Federer (1969), 3.4.8(1),(8), pp. 326, 329:
    the actual constant germs give the original
    scalar homomorphism. Reuse the established germ
    arithmetic, including the constant-product theorem
    of the Weierstrass normalization proof. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP AnalyticGermUP AnalyticGermSealed AnalyticGermRing AnalyticGermRingLaws
  AnalyticGermRepresentatives WeierstrassScalarGermArithmetic AnalyticScalarsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Constants.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Variable hNX:is_real_norm NX.
Variable a:X.
Local Notation G:=(@analytic_germ_ring R X NX hNX a).

(** Source for [analytic_scalar_germ_function]: private
    actual representative for the original scalar
    identification, 3.4.8(1), p. 326. *)
Definition analytic_scalar_germ_function (c:R):G:=
  analytic_germ (@analytic_constant_representative R X NX hNX a c).

(** Source for [analytic_scalar_germ_additive]: original
    zero and addition are preserved by the
    scalar identification, 3.4.8(1), p. 326. *)
Lemma analytic_scalar_germ_additive:nmod_morphism analytic_scalar_germ_function.
Proof.
split;first by [].
move=>c d;rewrite /analytic_scalar_germ_function.
change (analytic_germ (@analytic_constant_representative R X NX hNX a (c+d)) =
  @AnalyticGerms.add R X NX hNX a
    (analytic_germ (@analytic_constant_representative R X NX hNX a c))
    (analytic_germ (@analytic_constant_representative R X NX hNX a d))).
rewrite (@analytic_germ_add_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R X NX hNX a)).
apply:analytic_germ_pointwise_equality=>x;by [].
Qed.
HB.instance Definition _:=GRing.isNmodMorphism.Build R G analytic_scalar_germ_function analytic_scalar_germ_additive.

(** Source for [analytic_scalar_germ_multiplicative]: original
    scalar products retain the already proved
    constant-germ product formula, supporting
    3.4.8(1),(8), pp. 326, 329. *)
Lemma analytic_scalar_germ_multiplicative:monoid_morphism analytic_scalar_germ_function.
Proof.
split;first by [].
move=>c d;exact:esym (@weierstrass_constant_germ_product R X NX hNX a c d).
Qed.
HB.instance Definition _:=GRing.isMonoidMorphism.Build R G analytic_scalar_germ_function analytic_scalar_germ_multiplicative.

(** Source for [analytic_scalar_map_exists]: the original
    constant identification exists as a ring
    homomorphism, 3.4.8(1),(8), pp. 326, 329. *)
Theorem analytic_scalar_map_exists:exists scalar:{rmorphism R->G},is_analytic_scalar_map scalar.
Proof. exists (GRing.RMorphism.clone R G analytic_scalar_germ_function _)=>c;by []. Qed.
End Constants.

(** Source for [analytic_scalar_map_unique]: every original
    scalar representative determines the same image,
    3.4.8(1), p. 326. *)
Lemma analytic_scalar_map_unique (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) a
  (scalar other:{rmorphism R->@analytic_germ_ring R X NX hNX a}):
  is_analytic_scalar_map scalar ->is_analytic_scalar_map other ->forall c,scalar c = other c.
Proof. move=>hScalar hOther c;by rewrite hScalar hOther. Qed.
