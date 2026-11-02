(** Federer (1969), 2.6.4, p. 119: commutativity of the first
    tensor-integral diagram, after the total-domain correction in erratum p.
    2, book p. 119 lines 3, 4, 6. The pure-tensor identity extends by the
    tensor universal property, without computation through either sealed
    carrier. its tensor universal property is 3.5, pp. 21–23. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureIntegralUniqueness ProductMeasure
  SummableRealSpace SummableRealIntegralMap SummableTensorMap SeparatedProductIntegral
  TensorUP TensorProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Diagram.
Variable R : realType.
Variables X Y : choiceType.
Variables (alpha : set X -> \bar R) (beta : set Y -> \bar R).
Variables (ha : is_measure alpha) (hb : is_measure beta).
Local Notation U := (summable_real_space ha).
Local Notation V := (summable_real_space hb).

(** Source for [summable_product_integral_value]: the pure-tensor
    case of the commutative diagram in Federer 2.6.4,
    p. 119, with actual finite integral values. *)
Lemma summable_product_integral_value (f : U) (g : V) :
  summable_real_integral_map (summable_product_pair f g) =
  summable_real_integral_map f * summable_real_integral_map g.
Proof.
have hi := @separated_product_integral R X Y alpha beta ha hb
  (summable_real_value f) (summable_real_value g) _ _
  (summable_real_integral_map_specification f) (summable_real_integral_map_specification g).
have hj := summable_real_integral_map_specification (summable_product_pair f g).
have he : summable_real_value (summable_product_pair f g) =
    (fun p : X*Y => summable_real_value f p.1*summable_real_value g p.2).
  apply: funext=> p; exact: summable_product_pairE.
rewrite he in hj; exact: EFin_inj (measure_integral_unique hj hi).
Qed.

(** Source for [summable_integral_pair_bilinear]: supporting
    bilinearity of the scalar product of integral maps in
    Federer 2.6.4, p. 119. *)
Lemma summable_integral_pair_bilinear : bilinear
  (fun (f : U) (g : V) => (summable_real_integral_map f * summable_real_integral_map g : R^o)).
Proof.
split.
- move=> g c f h; rewrite linearP /=.
  change ((c*summable_real_integral_map f+summable_real_integral_map h)*summable_real_integral_map g =
    c*(summable_real_integral_map f*summable_real_integral_map g)+summable_real_integral_map h*summable_real_integral_map g).
  by rewrite mulrDl mulrA.
- move=> f c g h; rewrite linearP /=.
  change (summable_real_integral_map f*(c*summable_real_integral_map g+summable_real_integral_map h) =
    c*(summable_real_integral_map f*summable_real_integral_map g)+summable_real_integral_map f*summable_real_integral_map h).
  by rewrite mulrDr mulrCA.
Qed.

(** Source for [summable_integral_tensor]: the scalar tensor
    product of the two integral functionals in the first diagram
    of Federer 2.6.4, p. 119. *)
Definition summable_integral_tensor : {linear tensor_space U V -> R^o} :=
  GRing.Linear.clone _ _ _ _ (tensor_lift summable_integral_pair_bilinear) _.

(** Source for [summable_tensor_integral_diagram]: complete
    commutativity of the first diagram in Federer 2.6.4,
    p. 119, with his erratum's total-domain correction. *)
Theorem summable_tensor_integral_diagram t :
  summable_real_integral_map (summable_tensor_map ha hb t) = summable_integral_tensor t.
Proof.
apply: (tensor_ext (tensor_exists U V)
  (linear_comp (GRing.Linear.clone _ _ _ _
    (@summable_real_integral_map R (Choice.clone (X*Y)%type _) _ (product_measure_is_measure ha hb)) _)
    (summable_tensor_map ha hb)) summable_integral_tensor)=> f g /=.
by rewrite summable_tensor_map_generator summable_product_integral_value /summable_integral_tensor tensor_liftE.
Qed.
End Diagram.
