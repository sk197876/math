(** Federer (1969), 2.6.4, pp. 118–119: the function image of the
    total-domain L1 tensor map. Its linear closure and summability are
    exposed for the density proof. The total domain follows erratum p. 2,
    book p. 119 lines 3, 4, 6. the tensor spanning principle follows from
    his 4.10, pp. 40–41. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP ProductMeasure SummableRealFunctionUP SummableRealArithmetic
  SummableRealSpace FunctionProductBilinear TensorUP TensorProduct TensorSpan
  SeparatedProductIntegral LatticeL1ApproximationLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Image.
Variable R : realType.
Variables X Y : choiceType.
Variables (alpha : set X -> \bar R) (beta : set Y -> \bar R).
Variables (ha : is_measure alpha) (hb : is_measure beta).
Local Notation U := (summable_real_space ha).
Local Notation V := (summable_real_space hb).
Local Notation phi := (function_tensor_map (@summable_real_value R X alpha ha) (@summable_real_value R Y beta hb)).

(** Source for [separated_summable_image]: image in ordinary
    functions of the monomorphism in Federer 2.6.4, p. 118.
    It is specified through the abstract tensor map, retaining
    literal function values even on null sets. *)
Definition separated_summable_image : set ((X*Y) -> R) :=
  [set h | exists t : tensor_space U V, phi t=h].

(** Source for [separated_summable_image_zero]: supporting zero
    member of the linear image in Federer 2.6.4, p. 118. *)
Lemma separated_summable_image_zero : separated_summable_image (fun _ => 0).
Proof. exists 0; exact: linear0. Qed.

(** Source for [separated_summable_image_add]: supporting additive
    closure of the image used in the density proof of Federer
    2.6.4, pp. 118–119. *)
Lemma separated_summable_image_add f g :
  separated_summable_image f -> separated_summable_image g ->
  separated_summable_image (fun p => f p+g p).
Proof.
move=> [t <-] [s <-]; exists (t+s); by rewrite linearD /= addrfctE.
Qed.

(** Source for [separated_summable_image_scale]: supporting
    scalar closure in the density proof of Federer 2.6.4,
    pp. 118–119. Negative coefficients are included. *)
Lemma separated_summable_image_scale c f :
  separated_summable_image f -> separated_summable_image (fun p => c*f p).
Proof.
move=> [t <-]; exists (c *: t); by rewrite linearZ /= scalrfctE.
Qed.

(** Source for [separated_summable_image_subtract]: supporting
    difference closure for characteristic inclusion-exclusion in
    Federer 2.6.4, pp. 118–119. *)
Lemma separated_summable_image_subtract f g :
  separated_summable_image f -> separated_summable_image g ->
  separated_summable_image (fun p => f p-g p).
Proof.
move=> [t <-] [s <-]; exists (t-s); by rewrite linearB /= !fctE.
Qed.

(** Source for [separated_summable_image_product]: each product
    f(x)g(y) of summable functions belongs to the tensor image,
    Federer 2.6.4, p. 118. Representatives are chosen only
    through the abstract carrier's surjectivity law. *)
Lemma separated_summable_image_product (f : X -> R) (g : Y -> R) :
  summable_real_functions alpha f -> summable_real_functions beta g ->
  separated_summable_image (fun p : X*Y => f p.1*g p.2).
Proof.
move=> hf hg; exists (tensor_inj (summable_real_pack ha hf) (summable_real_pack hb hg)).
apply: funext=> p; by rewrite function_tensor_map_generator !summable_real_packE.
Qed.

(** Source for [separated_summable_image_summable]: the entire
    image lies in total-domain L1 of the product measure, as
    asserted in Federer 2.6.4, p. 118. *)
Lemma separated_summable_image_summable f :
  separated_summable_image f -> summable_real_functions (product_measure ha hb) f.
Proof.
move=> [t <-]; elim/tensor_induction: t=> [|t s ht hs|c t ht|a b].
- rewrite linear0; exists 0; exact: real_total_zero_integral (product_measure_is_measure ha hb).
- rewrite linearD /= addrfctE; exact (@summable_real_add R (Choice.clone (X*Y)%type _) _ (product_measure_is_measure ha hb) _ _ ht hs).
- rewrite linearZ /= scalrfctE; exact (@summable_real_scale R (Choice.clone (X*Y)%type _) _ (product_measure_is_measure ha hb) _ c ht).
- have he : phi (tensor_inj a b)=(fun p : X*Y => summable_real_value a p.1*summable_real_value b p.2).
    apply: funext=> p; exact: function_tensor_map_generator.
  rewrite he; exact (@separated_product_summable R X Y alpha beta ha hb _ _
    (summable_real_value_summable a) (summable_real_value_summable b)).
Qed.
End Image.
