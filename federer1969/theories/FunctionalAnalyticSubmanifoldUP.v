(** Federer (1969), 3.4.5, p. 321: functional
    analytic submanifolds and analytic blocks. The n-m equations
    retain the actual independent differentials; their indices
    correspond to the printed labels m+1 through n. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP Hom FiniteIndependence GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness NormMetric NormDifferentialUP NormAnalyticUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_functional_analytic_submanifold]: the
    original m-dimensional functional analytic submanifold of U,
    3.4.5, p. 321. Every defining function is
    analytic on the original U; the displayed differentials
    are actual and linearly independent at every original S
    point. The empty equation family retains m=n. *)
Definition is_functional_analytic_submanifold (R:realType) n m
    (U S:set (R_n R n)):Prop:=
  (m<=n)%N /\@open (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) U /\
  exists f:'I_(n-m)->R_n R n->R,exists g:R_n R n->R,
    (forall i,@norm_analytic R (R_n R n) R^o
      (inner_norm (@euclidean_inner_productP R n)) (fun z:R^o=>`|z|)
      (inner_norm_real_norm (@euclidean_inner_productP R n)) (@scalar_absolute_value_norm R) U (f i)) /\
    @norm_analytic R (R_n R n) R^o
      (inner_norm (@euclidean_inner_productP R n)) (fun z:R^o=>`|z|)
      (inner_norm_real_norm (@euclidean_inner_productP R n)) (@scalar_absolute_value_norm R) U g /\
    (forall x,S x <->U x /\(forall i,f i x=0) /\g x<>0) /\
    forall x,S x ->exists D:'I_(n-m)->Hom (R_n R n) R^o,
      (forall i,has_norm_differential (inner_norm (@euclidean_inner_productP R n)) (fun z:R^o=>`|z|)
        U (f i) x (D i)) /\finite_independent D.

(** Source for [is_functional_analytic_block]: the components
    of a functional analytic m-submanifold are the analytic
    m-blocks of U, 3.4.5, p. 321. The
    connected component is taken in the actual norm topology. *)
Definition is_functional_analytic_block (R:realType) n m
    (U B:set (R_n R n)):Prop:=
  exists S:set (R_n R n),is_functional_analytic_submanifold m U S /\
    exists a:R_n R n,S a /\
      B=@connected_component
        (Topological.clone (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) _) S a.
