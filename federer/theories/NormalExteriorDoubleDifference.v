(** Three-product identity of Federer (1969), 2.10.32, pp. 196–197. Combine
    the joint affine parallel-shift identity with the vanishing top-degree
    hyperplane term. The result is twice the symmetrised endpoint product as
    the difference of two original endpoint products. This file proves the
    algebraic equality before using any norm or supremum. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP OrthonormalFamilies LinearBasis ExteriorAlgebra
  ExteriorGrading FiniteExteriorPowers GradedComponents ExteriorParallelAffinity NormalHyperplaneTopProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [normal_exterior_double_difference]: direct
    algebraic equality underlying the displayed
    half-difference of products in 2.10.32,
    p. 197. It is written without division;
    the scalar and vector hypotheses retain the
    real inner-product setting of the book. *)
Theorem normal_exterior_double_difference (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (n : nat) (e v : 'I_n -> V) (a g : 'I_n -> R) (u : V) :
  is_basis e -> B u u= 1 -> (forall i, inner_coordinate hB u (v i)=0) ->
  e_lambda (fun i=>v i+(g i+2*a i)*:u) (ord_tuple n)-
    e_lambda (fun i=>v i+g i*:u) (ord_tuple n)=
    2*:e_lambda (fun i=>v i+a i*:u) (ord_tuple n).
Proof.
move=> he hu hv.
have hz := unit_normal_hyperplane_top_product_zero he hu hv.
have hword : exterior_word [seq v i | i <- ord_tuple n]=0.
  by rewrite -e_lambdaE hz linear0.
apply: val_inj.
change (component_val (e_lambda (fun i=>v i+(g i+2*a i)*:u) (ord_tuple n)-
  e_lambda (fun i=>v i+g i*:u) (ord_tuple n))=
  component_val (2*:e_lambda (fun i=>v i+a i*:u) (ord_tuple n))).
rewrite linearB linearZ.
change (component_val (e_lambda (fun i=>v i+(g i+2*a i)*:u) (ord_tuple n))-
  component_val (e_lambda (fun i=>v i+g i*:u) (ord_tuple n))=
  2*:component_val (e_lambda (fun i=>v i+a i*:u) (ord_tuple n))).
by rewrite !e_lambdaE exterior_parallel_shift_double_difference hword subr0.
Qed.
