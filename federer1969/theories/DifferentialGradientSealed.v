(** Opaque witness for the gradient equation of Federer (1969),
    3.1.1, p. 209. Both existence alternatives are proved privately. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom InnerProductUP InnerNorm NormDifferentialUP
  DifferentialGradientUP DifferentialGradientConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module Type DifferentialGradientSignature.
(** Source for [value]: the gradient vector of Federer 3.1.1, p. 209,
    exposed independently of its finite-coordinate or Hilbert witness. *)
Parameter value : forall (R : realType) (V : lmodType R)
  (B : V -> V -> R) (hB : is_inner_product B),
  differential_gradient_space hB -> forall L : Hom V R^o,
  norm_bounded_linear (inner_norm hB) (fun t : R^o => `|t|) L -> V.
(** Source for [laws]: the characterising equation of grad f(a),
    Federer 3.1.1, p. 209. *)
Parameter laws : forall (R : realType) (V : lmodType R)
  (B : V -> V -> R) (hB : is_inner_product B)
  (hspace : differential_gradient_space hB) (L : Hom V R^o)
  (hL : norm_bounded_linear (inner_norm hB) (fun t : R^o => `|t|) L),
  is_differential_gradient B L (@value R V B hB hspace L hL).
End DifferentialGradientSignature.

Module DifferentialGradient : DifferentialGradientSignature.
(** Source for [value]: private selection from the proved gradient
    existence theorem for Federer 3.1.1, p. 209. *)
Definition value (R : realType) (V : lmodType R)
  (B : V -> V -> R) (hB : is_inner_product B)
  (hspace : differential_gradient_space hB) (L : Hom V R^o)
  (hL : norm_bounded_linear (inner_norm hB) (fun t : R^o => `|t|) L) : V :=
  sval (constructive_indefinite_description
    (@differential_gradient_exists R V B hB hspace L hL)).
(** Source for [laws]: the selected witness satisfies the gradient
    equation of Federer 3.1.1, p. 209. *)
Lemma laws (R : realType) (V : lmodType R)
  (B : V -> V -> R) (hB : is_inner_product B)
  (hspace : differential_gradient_space hB) (L : Hom V R^o)
  (hL : norm_bounded_linear (inner_norm hB) (fun t : R^o => `|t|) L) :
  is_differential_gradient B L (@value R V B hB hspace L hL).
Proof. exact: (svalP (constructive_indefinite_description
  (@differential_gradient_exists R V B hB hspace L hL))). Qed.
End DifferentialGradient.
