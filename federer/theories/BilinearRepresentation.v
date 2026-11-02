(** Federer (1969), 1.7.3, pp. 29-30: representing the alternating two-form
    by an endomorphism and the inner product. The supporting representation
    works for every bilinear form, by the already established polarity
    isomorphism. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerPolarity InnerPolaritySurjection
  BilinearPolarity LinearBasis TensorUP AlternatingForms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [bilinear_endomorphism_representation]: Federer
    1.7.3, pp. 29-30, supporting existence of f satisfying
    f(x).y=S(x,y). The two-form application is a special case;
    finite dimension makes the inner-product polarity surjective. *)
Theorem bilinear_endomorphism_representation (R : rcfType) (V : lmodType R)
    (B S : V -> V -> R) (hB : is_inner_product B)
    (hS : @bilinear R V V R^o S) n (b : 'I_n -> V) (hb : is_basis b) :
  exists f : {linear V -> V}, forall x y, B (f x) y = S x y.
Proof.
pose T := fun x y => S y x.
have hT : @bilinear R V V R^o T by split; [exact hS.2 | exact hS.1].
pose p := GRing.Linear.clone _ _ _ _ (bilinear_polarity hT) _.
have hi := @inner_polarity_injective R V B hB.
have hs := @inner_polarity_surjective R V B hB n b hb.
pose g := linear_inverse hi hs.
exists (linear_comp g p); move=> x y.
rewrite (inner_symmetric hB) -(inner_polarityE hB).
change (inner_polarity hB (g (p x)) [tuple y] = S x y).
by rewrite /g linear_inverseK bilinear_polarityE.
Qed.
