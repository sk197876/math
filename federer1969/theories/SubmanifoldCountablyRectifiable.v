(** Federer (1969), 3.2.29, pp. 267–268:
    the easy direction uses the local Lipschitz
    parametrisations of class-one submanifolds. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanSubmanifoldUP
  SubmanifoldCountableCompactCover CompactSubmanifoldRectifiable RectifiableSetUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [submanifold_countably_rectifiable]: a
    class-k m-dimensional Euclidean submanifold,
    k>=1, is countably m-rectifiable, supporting
    Federer 3.2.29, pp. 267–268. A countable
    compact cover and actual local charts prove it,
    including m=0 and empty manifolds. *)
Theorem submanifold_countably_rectifiable (R:realType) n m k (S:set (R_n R n)):
  (1<=k)%N ->@is_euclidean_submanifold R n m k S ->
  @is_countably_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R n)) m S.
Proof.
move=>hk hS; have [K [hK hCover]]:=submanifold_countable_compact_cover hS.
exists (K @` setT); split.
- exact:sub_countable (card_image_le _ _) (countableP setT).
- split.
  + move=>A [i _ <-]; exact:compact_submanifold_rectifiable hk hS (hK i).2 (hK i).1.
  + rewrite hCover; apply/seteqP; split=>x.
    * move=>[i _ hx]; exists (K i); first by exists i.
      exact hx.
    * move=>[A [i _ <-] hx]; by exists i.
Qed.
