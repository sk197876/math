(** Federer (1969), 3.1.20, pp. 232–233: submanifolds admit
    neighbourhood retractions of their class. The construction uses
    the corrected intermediate maps and the sealed patching sequence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness NormMetric NormDifferentialUP NormRegularity
  NormRegularityOperations NormOpenDomainLaws RetractionUP EuclideanSubmanifoldUP
  SubmanifoldStraighteningCoordinates SubmanifoldPatchingFamily LocallyFiniteRetractionGluing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [zero_ambient_subset_retraction]: the singleton
    ambient-space boundary of the forward construction in Federer
    3.1.20, pp. 232–233. Every subset of R^0 is empty or the
    singleton, and has a neighbourhood retraction of every finite class. *)
Lemma zero_ambient_subset_retraction (R:realType) k (B:set (R_n R 0)) :
  exists (A:set (R_n R 0)) (f:R_n R 0->R_n R 0),
    @open [the topologicalType of real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R 0))] A /\
    is_norm_class_retraction (inner_norm_real_norm (@euclidean_inner_productP R 0)) A B f k.
Proof.
pose X:=R_n R 0.
pose NX:=inner_norm (@euclidean_inner_productP R 0).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R 0).
case:(pselect (exists b,B b))=>[[b hb]|hempty].
- exists setT,(fun _=>b); split; first exact: openT.
  constructor.
  + exact (@norm_class_constant R X X NX NX hNX hNX setT b k (fun x _=>norm_full_domain_interior NX x)).
  + by move=>x hx.
  + by move=>x hx.
  + move=>x hx; by rewrite (coordinate_zero b) (coordinate_zero x).
- exists set0,(fun _=>0); split; first exact: open0.
  constructor.
  + exact (@norm_class_constant R X X NX NX hNX hNX set0 0 k (fun x hx=>False_rect _ hx)).
  + move=>x hx; exfalso; apply: hempty; by exists x.
  + by move=>x [].
  + move=>x hx; exfalso; apply: hempty; by exists x.
Qed.

(** Source for [submanifold_neighbourhood_retraction]: the forward
    implication of Federer 3.1.20, pp. 232–233. The patching
    proof also covers class zero and does not use connectedness.
    The retraction's actual open domain contains all of B. *)
Theorem submanifold_neighbourhood_retraction (R:realType) n mu k (B:set (R_n R n)) :
  @is_euclidean_submanifold R n mu k B ->
  exists (A:set (R_n R n)) (f:R_n R n->R_n R n),
    @open [the topologicalType of real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n))] A /\
    is_norm_class_retraction (inner_norm_real_norm (@euclidean_inner_productP R n)) A B f k.
Proof.
case:n B=>[|n] B hB; first exact: zero_ambient_subset_retraction.
have hcharts:=submanifold_convex_coordinates hB.
have [U [P [Q [hF [hLF hcover]]]]]:=@submanifold_retraction_patch_family R n mu k B hcharts.
exact (@locally_finite_retractions_glue R (R_n R n.+1) (R_n R mu)
  (inner_norm (@euclidean_inner_productP R n.+1)) (inner_norm (@euclidean_inner_productP R mu))
  (inner_norm_real_norm (@euclidean_inner_productP R n.+1))
  (inner_norm_real_norm (@euclidean_inner_productP R mu)) B U P Q k hF hLF hcover).
Qed.
