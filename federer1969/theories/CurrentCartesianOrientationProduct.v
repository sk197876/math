(** Federer (1969), 4.1.8, p. 361: the original
    product of the two partial orienting fields. Use
    their actual domains and the original block inclusions;
    no arbitrary value is assigned outside either domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations ExteriorGrading EuclideanCartesianMap CurrentDomain
  CurrentCartesianDomainMapsSealed CurrentCartesianVectorProduct PartialFunctionUP PartialFunctionBasic
  PartialFunctionPrecomposition PartialFunctionPostcomposition PartialFunctionPair.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section CurrentCartesianOrientationProduct.
Variable R:realType.
Variables m n i j:nat.
Variables (A:set (R_n R m)) (B:set (R_n R n)).
Local Notation AT := (current_domain R m A).
Local Notation BT := (current_domain R n B).
Local Notation CT := (current_domain R (m+n) (@euclidean_cartesian_set R m n A B)).
Local Notation VA := (exterior_power (R_n R m) i).
Local Notation VB := (exterior_power (R_n R n) j).
Local Notation VC := (exterior_power (R_n R (m+n)) (i+j)).
Local Notation D := (@CartesianCurrentDomain.split R m n A B).
Local Notation F := (@current_cartesian_vector_product R m n i j).
Variables (phi:partial_function AT VA) (psi:partial_function BT VB).

(** Source for [current_cartesian_orientation_product]: the
    original partial density zeta(a,b), Federer 4.1.8,
    p. 361. Its value uses exactly the two original
    orienting-field values where both are defined. *)
Definition current_cartesian_orientation_product:partial_function CT VC:=
  partial_function_postcompose
    (partial_function_pair (partial_function_precompose (fun z:CT=>(D z).1) phi)
      (partial_function_precompose (fun z:CT=>(D z).2) psi))
    (fun v:VA*VB=>F v.1 v.2).

(** Source for [current_cartesian_orientation_product_graph]:
    the original product density has precisely the two
    original factor values and their included wedge,
    supporting Federer 4.1.8, p. 361. *)
Lemma current_cartesian_orientation_product_graph z w:
  partial_function_graph current_cartesian_orientation_product z w <->
  exists a:VA,exists b:VB,partial_function_graph phi (D z).1 a /\
    partial_function_graph psi (D z).2 b /\F a b=w.
Proof.
split.
- move=>[[a b] [[hA hB] hW]];by exists a,b.
- move=>[a [b [hA [hB hW]]]];exists (a,b);by split;first split.
Qed.

(** Source for [current_cartesian_orientation_product_domain]:
    the product density keeps exactly the common original
    factor-domain condition, supporting Federer 4.1.8,
    p. 361. No maximal-domain assertion is imposed on it. *)
Lemma current_cartesian_orientation_product_domain:
  partial_function_domain current_cartesian_orientation_product=
    [set z:CT|partial_function_domain phi (D z).1 /\partial_function_domain psi (D z).2].
Proof.
rewrite /current_cartesian_orientation_product partial_function_postcompose_domain partial_function_pair_domain
  !partial_function_precompose_domain;by [].
Qed.
End CurrentCartesianOrientationProduct.
