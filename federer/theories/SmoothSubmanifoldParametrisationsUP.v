(** Federer (1969), 3.1.19, p. 231: the four alternative local
    specifications (2)–(5). Equivalence with the straightening
    definition is an obligation proved separately, not a defining axiom. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNorm HilbertFormCompactness InnerConvex NormDifferentialUP
  NormClassOneUP NormRegularity NormMetric NormDiffeomorphismUP
  LinearRankUP OrthogonalMaps AdjointUP EuclideanSubmanifoldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Charts.
Variable R:realType.
Variable n:nat.
Local Notation E d:=(R_n R d).
Local Notation N d:=(inner_norm (@euclidean_inner_productP R d)).
Local Notation hN d:=(inner_norm_real_norm (@euclidean_inner_productP R d)).

(** Source for [has_smooth_open_constant_rank_parametrisations]:
    the smooth image arguments in Federer 3.2.28(2),(4),
    pp. 264,267, via 3.1.19(3), p. 231. One actual
    parameter map and differential field have every finite class. *)
Definition has_smooth_open_constant_rank_parametrisations mu (B:set (E n)) :=
  forall b, B b -> exists m (Q:set (E m)) (f:E m->E n) (D:E m->Hom (E m) (E n)),
    (mu<=m)%N /\ norm_class_all_orders (hN m) (hN n) Q f /\
    is_norm_class_one_field (N m) (N n) Q f D /\
    (forall x, Q x -> B (f x)) /\ (f @` Q) b /\
    (forall x, Q x -> has_linear_rank (D x) mu) /\
    forall W:set (E m), W `<=` Q -> @open [the topologicalType of real_norm_metric_space (hN m)] W ->
      @relatively_open_set [the topologicalType of real_norm_metric_space (hN n)] B (f @` W).

End Charts.
