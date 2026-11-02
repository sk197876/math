(** Federer (1969), 3.1.20, p. 233: a class-k retraction
    onto a connected subset has a submanifold image. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness NormMetric NormDifferentialUP NormClassOneUP NormRegularity
  RetractionUP EuclideanSubmanifoldUP RetractionMaximalRank RetractionGenericStraightening.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [class_retraction_submanifold]: the converse of
    Federer 3.1.20, pp. 232–233. Connectedness forces one
    maximal rank on B, and the actual constant-rank charts give
    straightening neighbourhoods. The empty set is handled separately. *)
Theorem class_retraction_submanifold (R:realType) n k
    (A B:set (R_n R n)) (f:R_n R n->R_n R n) :
  (1<=k)%N -> @connected [the topologicalType of real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R n))] B ->
  is_norm_class_retraction (inner_norm_real_norm (@euclidean_inner_productP R n)) A B f k ->
  exists mu,@is_euclidean_submanifold R n mu k B.
Proof.
move=>hk hB hR.
case:(pselect (exists b,B b))=>[[b hb]|hempty].
- pose NX:=inner_norm (@euclidean_inner_productP R n).
  pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
  have [D hD]:=(norm_class_firstP hNX hNX A f).1 (norm_class_lower hk (norm_retraction_class hR)).
  have hA:exists a,A a.
    exists b; exact (@norm_retraction_subset R (R_n R n) NX hNX A B f k hR b hb).
  have [mu [hmun hgeneric]]:=@connected_retraction_generic_rank R n k A B f D hB hR hD hA.
  exists mu=>x hx.
  exact (@retraction_generic_straightening R n mu k A B f D x hk hR hD hx (hgeneric x hx)).
- exists 0%N=>b hb; exfalso; apply: hempty; by exists b.
Qed.
