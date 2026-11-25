(** Federer (1969), 3.2.22, pp. 258–259: supporting
    agreement of intrinsic exterior-word norms and ordinary
    induced exterior operator norms on actual linear domains. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanLinearMaps EuclideanLinearJacobian PartialFunctionUP PartialFunctionBasic
  PartialExteriorNormUP ExteriorNorm ExteriorMaps ExteriorOperatorEstimate ExteriorOperatorNorm
  OperatorNormUP ExteriorUnitWordOperatorBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [partial_exterior_total_linear_norm]: the
    approximate exterior norm used in Federer 3.2.22,
    p. 258, agrees with the usual exterior operator
    norm when its actual partial graph is a total linear
    map. Every natural exterior degree is included. *)
Lemma partial_exterior_total_linear_norm (R:realType) m n q
    (L:Hom (R_n R m) (R_n R n)):
  is_partial_exterior_norm q (partial_function_total L) (euclidean_linear_jacobian q L).
Proof.
constructor; first exact:euclidean_linear_jacobian_nonnegative.
- move=>v w hGraph hUnit.
  have hW:w=(fun i=>L (v i)) by apply:funext=>i; exact:esym (hGraph i).
  rewrite hW -exterior_map_indexed_product.
  exact:(operator_norm_unit_bound (exterior_operator_normP (euclidean_two_nonzero R)
    (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
    (@coordinate_basisP R m) (hom_as_linear L) q) hUnit).
- move=>J hJ hBound; apply:(exterior_unit_word_operator_bound
    (@coordinate_basisP R m) hJ)=>v hUnit.
  apply:(hBound v (fun i=>L (v i)) _ hUnit)=>i; reflexivity.
Qed.
