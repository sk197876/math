(** Federer (1969), 3.2.33, p. 270: on the full
    Euclidean approximate tangent, the actual partial-image dimension
    is the rank of the actual ordinary linear differential. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom ModuleQuotient SubspaceSums SubspaceCarrier SubspaceEquality
  GrassmannAbbreviations GrassmannSubspaces PartialFunctionUP PartialFunctionBasic
  PartialMetricLipschitz LinearRankUP PartialImageDimensionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [partial_total_linear_low_image_iff]: the
    dimension condition defining X in Federer 3.2.32,
    p. 269, specialized to the total actual differential
    of the smooth map in 3.2.33, p. 270. The
    two independently defined range predicates give the same
    subspace. Existing basis laws identify their dimensions;
    no image plane is selected globally. *)
Lemma partial_total_linear_low_image_iff (R:realType) m n mu
    (L:Hom (R_n R m) (R_n R n)):
  is_partial_image_dimension_at_most mu (partial_function_total L) <->
  exists r,has_linear_rank L r /\(r<=mu)%N.
Proof.
have hRange:partial_function_range (partial_function_total L)=
    [set y|range_subspace (hom_as_linear L) y].
  apply/seteqP; split=>y [x hx]; exists x; exact:(esym hx).
split.
- move=>[r [P [hr hImage]]].
  have hSub:range_subspace (hom_as_linear L)=grassmann_val P.
    apply:subspace_ext=>y.
    change (([set z|range_subspace (hom_as_linear L) z]) y<->([set z|grassmann_val P z]) y).
    by rewrite -hRange hImage.
  exists r; split; last exact hr.
  rewrite /has_linear_rank hSub; exact:(grassmann_proof P).
- move=>[r [hRank hr]].
  pose P:=@GrassmannSubspace R (R_n R n) r (range_subspace (hom_as_linear L)) hRank.
  exists r,P; split; first exact hr.
  exact hRange.
Qed.
