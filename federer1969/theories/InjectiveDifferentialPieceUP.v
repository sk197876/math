(** Federer (1969), 3.2.2, p. 242: intrinsic laws for the
    Borel pieces and the countable cover of the injective
    differentiability locus. No cover or inverse is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness NormMetric NormDifferentialUP EuclideanLinearMaps
  EuclideanLinearJacobian PartialFunctionUP TopologicalBorel LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [injective_differential_locus]: the set covered
    in Federer 3.2.2, p. 242. Membership means that
    an actual ordinary differential exists and is injective. *)
Definition injective_differential_locus (R:realType) m n
    (f:R_n R m->R_n R n):set (R_n R m):=
  [set a|exists D:Hom (R_n R m) (R_n R n),
    has_norm_differential (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n)) setT f a D /\ injective D].

(** Source for [is_injective_differential_piece]: the Borel
    set E and source automorphism s with the four displayed
    estimates in Federer 3.2.2, p. 242. Exact inverse
    graphs retain only their proper image domains. *)
Definition is_injective_differential_piece (R:realType) m n
    (f:R_n R m->R_n R n) (lambda:R) (E:set (R_n R m)):Prop:=
  @borel_set [the topologicalType of real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R m))] E /\
  E `<=` injective_differential_locus f /\
  {in E &,injective f} /\
  exists (s t:Hom (R_n R m) (R_n R m)) (g:partial_function (R_n R n) (R_n R m)),
    cancel s t /\ cancel t s /\
    (forall y x,partial_function_graph g y x <-> E x /\ f x=y) /\
    @is_metric_lipschitz_bound R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (s @` E) (fun y=>f (t y)) lambda /\
    (forall y z x w,partial_function_graph g y x -> partial_function_graph g z w ->
      inner_norm (@euclidean_inner_productP R m) (s x-s w)<=
        lambda*inner_norm (@euclidean_inner_productP R n) (y-z)) /\
    forall x,E x -> forall D:Hom (R_n R m) (R_n R n),
      has_norm_differential (inner_norm (@euclidean_inner_productP R m))
        (inner_norm (@euclidean_inner_productP R n)) setT f x D ->
      (forall v,lambda^-1*inner_norm (@euclidean_inner_productP R m) (s v)<=
        inner_norm (@euclidean_inner_productP R n) (D v) /\
        inner_norm (@euclidean_inner_productP R n) (D v)<=
          lambda*inner_norm (@euclidean_inner_productP R m) (s v)) /\
      lambda^-1^+m*`|euclidean_det (hom_as_linear s)|<=euclidean_linear_jacobian m D /\
      euclidean_linear_jacobian m D<=lambda^+m*`|euclidean_det (hom_as_linear s)|.

(** Source for [is_injective_differential_cover]: the countable
    covering G of Federer 3.2.2, p. 242. The union
    is exactly the injective differentiability locus, and every
    member satisfies the Borel, inverse and distortion laws. *)
Definition is_injective_differential_cover (R:realType) m n
    (f:R_n R m->R_n R n) (lambda:R) (G:set (set (R_n R m))):Prop:=
  countable G /\ (\bigcup_(E in G) E)=injective_differential_locus f /\
  forall E,G E -> is_injective_differential_piece f lambda E.
