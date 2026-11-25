(** Federer (1969), 1.7.5, p. 32: supporting zero-factor and scaling laws
    for exterior products in the norm estimates. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ExteriorAlgebra ExteriorGrading ExteriorExpansion
  FiniteExteriorPowers GradedComponents Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [exterior_word_zero_factor]: Federer 1.7.5,
    p. 32, supporting zero-factor case of the product-norm
    inequality: a word containing the zero vector vanishes. *)
Lemma exterior_word_zero_factor (R : fieldType) (V : lmodType R) (s : seq V) :
  0 \in s -> exterior_word s = 0.
Proof.
elim: s => [|v s ih] //=; move/orP=> [/eqP hv|hs].
- by rewrite -hv exterior_word_cons linear0 (bil0l (wedge_bilinear V)).
- by rewrite exterior_word_cons (ih hs) (bil0r (wedge_bilinear V)).
Qed.

(** Source for [exterior_product_zero_entry]: Federer
    1.7.5, p. 32, a zero entry in an indexed exterior product
    makes that product zero, for any index set and degree. *)
Lemma exterior_product_zero_entry (R : fieldType) (I : choiceType)
    (V : lmodType R) (e : I -> V) m (t : m.-tuple I) i :
  i \in t -> e i = 0 -> e_lambda e t = 0.
Proof.
move=> hi hz; apply: val_inj.
change (component_val (e_lambda e t) = component_val (0 : exterior_power V m)).
rewrite e_lambdaE linear0; apply: exterior_word_zero_factor.
apply/mapP; exists i => //; exact: esym hz.
Qed.

(** Source for [exterior_product_scaled_family]: Federer
    1.7.5, p. 32, supporting normalisation step: scaling each
    vector multiplies the exterior product by the product of scalars. *)
Lemma exterior_product_scaled_family (R : fieldType) (V : lmodType R)
    m (e : 'I_m -> V) (c : 'I_m -> R) :
  e_lambda (fun i => c i *: e i) (ord_tuple m) =
    (\prod_i c i) *: e_lambda e (ord_tuple m).
Proof.
apply: val_inj.
change (component_val (e_lambda (fun i => c i *: e i) (ord_tuple m)) =
  component_val ((\prod_i c i) *: e_lambda e (ord_tuple m))).
rewrite linearZ e_lambdaE exterior_word_scaled.
change ((\prod_(i <- ord_tuple m) c i) *: exterior_word [seq e i | i <- ord_tuple m] =
  (\prod_i c i) *: component_val (e_lambda e (ord_tuple m))).
rewrite e_lambdaE; congr (_ *: _).
by rewrite /ord_tuple /= product_index_enum.
Qed.
