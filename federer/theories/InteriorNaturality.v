(** Federer (1969), 1.6.5, pp. 25-26, comparison of contractions under the
    displayed linear maps. Supporting naturality laws for the interior
    operations defined in 1.5.1, pp. 21-22. These supporting laws do not
    assert the product-space formula of 1.6.5 itself. All spaces here may
    have arbitrary dimension. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SimpleVectors.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [contract_tensor_natural]: Federer 1.5.1, p. 22,
    commutative contraction diagram, as used in 1.6.5, pp. 25-26.
    Supporting tensor identity: applying a map after scalar contraction
    is the same as mapping both tensor factors and pulling back the
    contracting functional. *)
Lemma contract_tensor_natural (K : fieldType) (X Y Z W : lmodType K)
  (f : {linear X -> Z}) (g : {linear Y -> W}) (a : Hom Z K^o)
  (t : tensor_space X Y) :
  (@contract_tensor K Z W a) (tensor_map f g t) =
    g ((@contract_tensor K X Y (hom_comp a (hom_of_linear f))) t).
Proof.
apply: (tensor_ext (tensor_exists X Y)
  (linear_comp ((@contract_tensor K Z W a)) (tensor_map f g))
  (linear_comp g ((@contract_tensor K X Y (hom_comp a (hom_of_linear f)))))) t => x y.
change ((@contract_tensor K Z W a) (tensor_map f g (tensor_inj x y)) =
  g ((@contract_tensor K X Y (hom_comp a (hom_of_linear f))) (tensor_inj x y))).
by rewrite tensor_mapE !contract_tensorE linearZ.
Qed.

(** Source for [left_interior_hom_natural]: Federer 1.6.5,
    pp. 25-26, induced maps and contraction. Supporting naturality
    law on the whole exterior algebra, derived from the diagonal
    map and scalar contraction in 1.5.1, p. 22. *)
Theorem left_interior_hom_natural (K : fieldType) (h2 : (1+1 : K) != 0)
  (V W : lmodType K) (f : {linear V -> W}) z (a : Hom (exterior_space W) K^o) :
  exterior_algebra_map f
    (left_interior_hom h2 z (hom_comp a (hom_of_linear (exterior_algebra_map f)))) =
  left_interior_hom h2 (exterior_algebra_map f z) a.
Proof.
by rewrite /left_interior_hom Psi_natural contract_tensor_natural.
Qed.

(** Source for [left_interior_natural]: Federer 1.6.5, pp. 25-26,
    induced exterior maps in the displayed identity. Supporting
    degree-specific naturality law: pushing forward a contraction
    against a pulled-back form equals contracting the pushforward. *)
Theorem left_interior_natural (K : fieldType) (h2 : (1+1 : K) != 0)
  (V W : lmodType K) (f : {linear V -> W}) p q (hpq : (p <= q)%N)
  (z : exterior_power V q) (a : A_m W K^o p) :
  exterior_power_map f (q-p) (left_interior h2 hpq z (A_m_dual f a)) =
    left_interior h2 hpq (exterior_power_map f q z) a.
Proof.
apply: val_inj.
change (exterior_algebra_map f
  (left_interior_hom h2 (component_val z) (form_homogeneous (A_m_dual f a))) =
  left_interior_hom h2 (exterior_algebra_map f (component_val z)) (form_homogeneous a)).
have ha : (form_homogeneous (A_m_dual f a) : Hom (exterior_space V) K^o) =
  hom_comp (form_homogeneous a) (hom_of_linear (exterior_algebra_map f)).
  apply: hom_ext => x.
  by rewrite /A_m_dual homogeneous_formK homogeneous_precomposeE.
rewrite ha; exact: left_interior_hom_natural.
Qed.

(** Source for [right_interior_natural]: Federer 1.6.5, pp. 25-26,
    induced maps and D_p. Supporting naturality identity for the
    right contraction defining D_p in 1.5.2, pp. 22-23. *)
Theorem right_interior_natural (K : fieldType) (V W Z : lmodType K)
  (f : {linear V -> W}) p q (hpq : (p <= q)%N)
  (x : exterior_power V p) (a : A_m W Z q) :
  right_interior hpq x (A_m_dual f a) =
    A_m_dual f (right_interior hpq (exterior_power_map f p x) a).
Proof.
apply: pairing_ext => y.
rewrite A_m_dual_pairing !right_interior_characteristic.
change (form_homogeneous (A_m_dual f a)
  (wedge (component_val y) (component_val x)) =
  form_homogeneous a (wedge (exterior_algebra_map f (component_val y))
    (exterior_algebra_map f (component_val x)))).
rewrite /A_m_dual homogeneous_formK homogeneous_precomposeE.
by rewrite (algebra_map_mul (exterior_algebra_map f)).
Qed.
