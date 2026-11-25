(** Federer (1969), 4.1.25, p. 383: specify the
    vector fibre sum by all original covector pairings,
    using the exact signed numerical sums of 2.1.1(4),
    p. 52, and 3.2.3(2), p. 243. The coefficient
    space is the actual finite exterior power. Existence
    and measurability of the area density remain separate. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading AlternatingForms AlternatingPairing CurrentCoefficientNorms
  CurrentMultivectorDual MultivectorDualSealed ContinuousDualUP
  PartialFunctionUP PartialFunctionPostcomposition PartialFibreNumericalSum
  ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section AreaFibreSum.
Variable R : realType.
Variable X : choiceType.
Variables n m : nat.
Local Notation Y := (R_n R n).
Local Notation V := (exterior_power Y m).
Local Notation A := (A_m Y R^o m).
Variable f : X -> Y.
Variable u : partial_function X V.

(** Source for [current_area_fibre_pairing_integrand]:
    evaluate the original vector summand on one fixed
    target covector, supporting Federer 4.1.25, p. 383.
    Composition keeps its entire original partial domain,
    including when the covector is zero. *)
Definition current_area_fibre_pairing_integrand (a : A) :
    partial_function X (extended_real_line R) :=
  partial_function_postcompose u
    (fun v => ((pairing v a)%:E : extended_real_line R)).

(** Source for [is_current_area_fibre_sum]: the original
    finite-dimensional vector sum in Federer 4.1.25,
    p. 383, specified through its scalar pairings. Each
    scalar sum has the exact original fibre and input
    domain. Undefined summands get no default value. *)
Definition is_current_area_fibre_sum (y : Y) (eta : V) : Prop :=
  forall a : A, partial_function_graph
    (partial_fibre_numerical_sum f (current_area_fibre_pairing_integrand a))
    y (pairing eta a)%:E.

(** Source for [current_area_fibre_sum_unique]: the original
    vector fibre sum of Federer 4.1.25, p. 383,
    is unique. Reuse the previously proved actual finite
    multivector dual; no general basis theorem is needed. *)
Theorem current_area_fibre_sum_unique (h2 : (1+1 : R) != 0) y (eta zeta : V) :
  is_current_area_fibre_sum y eta ->
  is_current_area_fibre_sum y zeta -> eta = zeta.
Proof.
move=> hEta hZeta.
apply: (continuous_dual_injective (@current_multivector_continuous_dual R h2 n m)).
apply: hom_ext => a; rewrite !MultivectorDual.laws.
exact: EFin_inj (partial_function_single_valued (hEta a) (hZeta a)).
Qed.

(** Source for [current_area_fibre_sum_input_domain]: every
    point of a defined fibre sum belongs to the original
    summand's domain, as required by the displayed formula
    of Federer 4.1.25, p. 383. A zero scalar pairing
    does not supply an undefined input value. *)
Theorem current_area_fibre_sum_input_domain y eta :
  is_current_area_fibre_sum y eta ->
  forall x, f x = y -> partial_function_domain u x.
Proof.
move=> hSum x hx.
have hZeroPairing := hSum (0 : A).
have [w [hW _]] := (@partial_fibre_numerical_sum_graph R X Y f
  (current_area_fibre_pairing_integrand 0) y (pairing eta (0 : A))%:E).1 hZeroPairing.
have hDomain : partial_function_domain (current_area_fibre_pairing_integrand 0) x.
  exists (w x); exact: hW x hx.
by rewrite /current_area_fibre_pairing_integrand
  partial_function_postcompose_domain in hDomain.
Qed.
End AreaFibreSum.
