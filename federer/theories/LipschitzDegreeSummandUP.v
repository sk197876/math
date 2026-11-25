(** Federer (1969), 4.1.26, p. 383: the
    signed determinant summand on A. Outside A
    it is zero; inside A it is defined
    exactly where the original differential exists,
    including zero determinant. No differential is
    supplied at an undefined source point. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanLinearMaps
  PartialFunctionUP PartialFunctionExtensionality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_lipschitz_degree_summand]: the original
    sign det Df(x) on A, extended by zero
    off A for the literal fibre sum of
    4.1.26, p. 383. Critical points with an
    existing differential retain their zero sign. *)
Definition is_lipschitz_degree_summand (R:realType) m
    (f:R_n R m->R_n R m) (A:set (R_n R m))
    (u:partial_function (R_n R m) R):Prop:=
  forall x a,partial_function_graph u x a<->
    (~A x /\a=0) \/
    (A x /\exists D:Hom (R_n R m) (R_n R m),
      has_norm_differential (inner_norm (@euclidean_inner_productP R m))
        (inner_norm (@euclidean_inner_productP R m)) (fun _=>True) f x D /\
      Num.sg (@euclidean_det R m (hom_as_linear D))=a).

(** Source for [lipschitz_degree_summand_unique]: the original
    signed differential summand has one exact partial
    graph, supporting 4.1.26, p. 383. *)
Theorem lipschitz_degree_summand_unique (R:realType) m f A
    (u v:partial_function (R_n R m) R):
  is_lipschitz_degree_summand f A u->is_lipschitz_degree_summand f A v->u=v.
Proof.
move=>hU hV;apply:partial_function_graph_extensionality=>x a.
by rewrite (hU x a) (hV x a).
Qed.
