(** Federer (1969), 1.7.9, p. 35, the displayed computation of the product
    of Gamma(f) and Gamma(g). *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP TensorUP TensorProduct TensorInner
  OrthonormalFamilies Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [tensor_inner_orthonormal_contraction]: Federer
    1.7.9, p. 35, first displayed sum: orthonormality in the first
    tensor factor reduces the double sum to a single sum. *)
Theorem tensor_inner_orthonormal_contraction (R : rcfType)
    (V W : lmodType R) (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    (I : finType) (e : I -> V) (he : orthonormal_family B e)
    (f g : I -> W) :
  tensor_inner hB hC (\sum_i tensor_inj (e i) (f i))
    (\sum_i tensor_inj (e i) (g i)) = \sum_i C (f i) (g i).
Proof.
have hD := inner_bilinear (tensor_inner_productP hB hC).
rewrite (big_morph (fun x => tensor_inner hB hC x (\sum_i tensor_inj (e i) (g i)))
  (fun x y => bilDl hD x y _) (bil0l hD _)).
apply: eq_bigr => i _.
rewrite (big_morph (fun y => tensor_inner hB hC (tensor_inj (e i) (f i)) y)
  (bilDr hD _) (bil0r hD _)).
rewrite (bigD1 i) //= tensor_innerE he eqxx mul1r.
have hz : (\sum_(j | j != i) tensor_inner hB hC
    (tensor_inj (e i) (f i)) (tensor_inj (e j) (g j))) = 0.
  apply: big1 => j hj; by rewrite tensor_innerE he eq_sym (negbTE hj) mul0r.
by rewrite hz addr0.
Qed.
