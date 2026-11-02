(** Federer (1969), 2.6.4, pp. 118–119: the L1 tensor map, with the
    total-domain convention required by erratum p. 2, book p. 119 lines 3,
    4, 6. Both L1 carriers and the tensor product are used only through
    their abstract sealed interfaces. the universal property is 4.10, pp.
    40–41. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP ProductMeasure SummableRealSpace SeparatedProductIntegral
  TensorUP TensorProduct TensorSpan FunctionProductBilinear FunctionTensorInjectivity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section TensorMap.
Variable R : realType.
Variables X Y : choiceType.
Variables (alpha : set X -> \bar R) (beta : set Y -> \bar R).
Variables (ha : is_measure alpha) (hb : is_measure beta).
Local Notation U := (summable_real_space ha).
Local Notation V := (summable_real_space hb).
Local Notation W := (summable_real_space (product_measure_is_measure ha hb)).

(** Source for [summable_product_pair]: the bilinear map at
    the beginning of Federer 2.6.4, p. 118, now taking
    values in the actual abstract total-domain L1 carrier. *)
Definition summable_product_pair (f : U) (g : V) : W :=
  summable_real_pack (product_measure_is_measure ha hb)
    (separated_product_summable ha hb (summable_real_value_summable f) (summable_real_value_summable g)).

(** Source for [summable_product_pairE]: the defining product
    formula h(x,y)=f(x)g(y) in Federer 2.6.4, p. 118. *)
Lemma summable_product_pairE f g p :
  summable_real_value (summable_product_pair f g) p =
  summable_real_value f p.1 * summable_real_value g p.2.
Proof. by rewrite /summable_product_pair summable_real_packE. Qed.

(** Source for [summable_product_pair_bilinear]: bilinearity
    asserted in Federer 2.6.4, p. 118, with no
    quotient by almost-everywhere equality. *)
Lemma summable_product_pair_bilinear : bilinear summable_product_pair.
Proof.
split.
- move=> g c f h; apply: summable_real_value_injective; apply: funext=> p; case: p=> x y.
  rewrite linearP /= !fctE /= !summable_product_pairE linearP /= !fctE /=.
  change ((c*summable_real_value f x+summable_real_value h x)*summable_real_value g y =
    c*(summable_real_value f x*summable_real_value g y)+summable_real_value h x*summable_real_value g y).
  by rewrite mulrDl mulrA.
- move=> f c g h; apply: summable_real_value_injective; apply: funext=> p; case: p=> x y.
  rewrite linearP /= !fctE /= !summable_product_pairE linearP /= !fctE /=.
  change (summable_real_value f x*(c*summable_real_value g y+summable_real_value h y) =
    c*(summable_real_value f x*summable_real_value g y)+summable_real_value f x*summable_real_value h y).
  by rewrite mulrDr mulrCA.
Qed.

(** Source for [summable_tensor_map]: the induced linear map
    of Federer 2.6.4, p. 118. Its construction is the
    abstract tensor lift from 1.1.1, p. 9. *)
Definition summable_tensor_map : {linear tensor_space U V -> W} :=
  GRing.Linear.clone _ _ _ _ (tensor_lift summable_product_pair_bilinear) _.

(** Source for [summable_tensor_map_generator]: the pure-tensor
    identity for the monomorphism in Federer 2.6.4, p. 118. *)
Lemma summable_tensor_map_generator f g :
  summable_tensor_map (tensor_inj f g)=summable_product_pair f g.
Proof. exact: tensor_liftE. Qed.

(** Source for [summable_tensor_map_function]: supporting
    compatibility with the unrestricted function tensor map in
    Federer 2.6.4, p. 118. The proof uses tensor uniqueness. *)
Lemma summable_tensor_map_function t :
  summable_real_value (summable_tensor_map t) =
  function_tensor_map (@summable_real_value R X alpha ha) (@summable_real_value R Y beta hb) t.
Proof.
apply: (tensor_ext (tensor_exists U V)
  (linear_comp (@summable_real_value R (Choice.clone (X*Y)%type _) _ (product_measure_is_measure ha hb)) summable_tensor_map)
  (function_tensor_map (@summable_real_value R X alpha ha) (@summable_real_value R Y beta hb)))=> f g /=.
rewrite summable_tensor_map_generator; apply: funext=> p.
by rewrite summable_product_pairE function_tensor_map_generator.
Qed.

(** Source for [summable_tensor_map_injective]: the complete
    linear monomorphism assertion of Federer 2.6.4, p. 118,
    for the total-domain spaces required by his erratum. *)
Theorem summable_tensor_map_injective : injective summable_tensor_map.
Proof.
move=> t s he.
apply: (function_tensor_map_injective (@summable_real_value_injective R X alpha ha)
  (@summable_real_value_injective R Y beta hb)).
by rewrite -!summable_tensor_map_function he.
Qed.
End TensorMap.
