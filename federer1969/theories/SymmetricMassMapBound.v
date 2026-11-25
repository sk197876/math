(** Federer (1969), 1.10.5, p. 48: supporting functorial estimate for the
    finite-decomposition mass. This is the estimate used when their bounded
    retraction is applied to a symmetric power. We prove it directly from
    the infimum laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import TensorUP AlgebraUP GradedComponents SymmetricAlgebra
  SymmetricGrading SymmetricMaps SymmetricPowerFunctor SymmetricFormIsomorphism
  RealNormUP RealSeminormOperations SymmetricDecompositionCosts SymmetricProjectiveMass
  SymmetricProjectiveSeminorm SymmetricProjectiveMaximality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_tuple_component_natural]: Federer 1.10.5,
    p. 48, supporting transport of a finite decomposition. The
    induced symmetric power sends a product to the product of the
    images of its factors, as defined in 1.9.1, pp. 41-42. *)
Lemma symmetric_tuple_component_natural (K : fieldType) (V W : lmodType K)
    (f : {linear V -> W}) m (t : m.-tuple V) :
  symmetric_power_map f m (symmetric_tuple_component t) =
    symmetric_tuple_component (map_tuple f t).
Proof.
apply: val_inj.
change (symmetric_algebra_map f (component_val (symmetric_tuple_component t)) =
  component_val (symmetric_tuple_component (map_tuple f t))).
by rewrite !symmetric_tuple_componentE symmetric_algebra_map_word.
Qed.

(** Source for [symmetric_projective_mass_map_bound]: Federer 1.10.5, p. 48,
    supporting bounded-retraction estimate. A linear map bounded by C
    induces a degree-m map bounded by C to the power m for mass. Input and
    output seminorms and arbitrary dimensions are allowed. *)
Theorem symmetric_projective_mass_map_bound (R : realType) (V W : lmodType R)
    (NV : V -> R) (NW : W -> R) (hV : is_real_seminorm NV) (hW : is_real_seminorm NW)
    (f : {linear V -> W}) C (hC : 0 <= C) (hf : forall v, NW (f v) <= C * NV v)
    m (hm : (0<m)%N) (x : symmetric_power V m) :
  symmetric_projective_mass hW hm (symmetric_power_map f m x) <=
    C^+m * symmetric_projective_mass hV hm x.
Proof.
have hQ := @real_seminorm_linear_precompose R (symmetric_power V m)
  (symmetric_power W m) (symmetric_projective_mass hW hm)
  (symmetric_projective_mass_seminorm hW hm)
  (symmetric_power_map f m) (linearP (symmetric_power_map f m)).
apply: (@symmetric_projective_mass_maximal R V NV hV m hm _ hQ
  (C^+m) (exprn_ge0 _ hC) _ x).
move=> t; rewrite symmetric_tuple_component_natural.
apply: le_trans (symmetric_projective_mass_tuple_bound hW hm (map_tuple f t)) _.
rewrite /symmetric_tuple_cost.
have he : C^+m * \prod_(i<m) NV (tnth t i) =
    \prod_(i<m) (C * NV (tnth t i)).
  by rewrite big_split prodr_const card_ord.
rewrite he; apply: ler_prod=> i _; rewrite tnth_map.
apply/andP; split; first exact: real_seminorm_nonnegative hW (f (tnth t i)).
exact: hf.
Qed.
