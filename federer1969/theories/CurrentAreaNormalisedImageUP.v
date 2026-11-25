(** Federer (1969), 4.1.25, p. 383: the normalized
    summand Lambda_m Df(x)(xi(x))/J_m f(x) is used on the
    original differentiability locus where Df is univalent.
    Specify its partial graph before proving existence.
    No value is assigned at an undefined differential or
    a zero Jacobian. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading ExteriorMaps EuclideanLinearJacobian
  PartialFunctionUP PartialFunctionExtensionality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_area_normalised_image_coefficient]:
    the normalized exterior differential expression in
    Federer 4.1.25, p. 383. This algebraic formula is
    used only under the nonzero-Jacobian condition in
    the independent partial-graph specification below. *)
Definition current_area_normalised_image_coefficient (R : realType) m n
    (xi : R_n R m -> exterior_power (R_n R m) m)
    (x : R_n R m) (D : Hom (R_n R m) (R_n R n)) :
    exterior_power (R_n R n) m :=
  (@euclidean_linear_jacobian R m n m D)^-1 *:
    exterior_power_map (hom_as_linear D) m (xi x).

(** Source for [is_current_area_normalised_image]: the
    exact original differential and nonzero-Jacobian
    domain of the summand in Federer 4.1.25, p. 383.
    Measurability, summability and the exceptional-image
    assertions are separate proof obligations. *)
Definition is_current_area_normalised_image (R : realType) m n
    (f : R_n R m -> R_n R n)
    (xi : R_n R m -> exterior_power (R_n R m) m)
    (u : partial_function (R_n R m) (exterior_power (R_n R n) m)) : Prop :=
  forall x v, partial_function_graph u x v <->
    exists D : Hom (R_n R m) (R_n R n),
      has_norm_differential (inner_norm (@euclidean_inner_productP R m))
        (inner_norm (@euclidean_inner_productP R n)) (fun _ => True) f x D /\
      @euclidean_linear_jacobian R m n m D != 0 /\
      current_area_normalised_image_coefficient xi x D = v.

(** Source for [current_area_normalised_image_unique]: the
    original differential summand in Federer 4.1.25,
    p. 383, determines one partial graph. Undefined
    points remain outside that graph. *)
Theorem current_area_normalised_image_unique (R : realType) m n f xi
    (u v : partial_function (R_n R m) (exterior_power (R_n R n) m)) :
  is_current_area_normalised_image f xi u ->
  is_current_area_normalised_image f xi v -> u = v.
Proof.
move=> hU hV; apply: partial_function_graph_extensionality => x a.
by rewrite (hU x a) (hV x a).
Qed.
