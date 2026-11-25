(** Federer (1969), 3.2.35, p. 271:
    the actual open set and its boundary are
    unchanged in the equivalent inner-product and
    own-norm topology interfaces. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import InnerProductUP InnerNorm InnerMetric HilbertFormCompactness NormMetric FiniteNormEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [inner_own_norm_open_iff]: supporting
    the original open-body hypothesis in Federer
    3.2.35, p. 271. The already proved
    equality of neighbourhood filters for the
    actual inner product and its own norm,
    1.7.1, p. 28, gives both open-set
    implications without a new topology. *)
Lemma inner_own_norm_open_iff (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) (A:set V):
  @open [the topologicalType of inner_metric_space hB] A <->
  @open [the topologicalType of real_norm_metric_space (inner_norm_real_norm hB)] A.
Proof.
split=>hOpen; rewrite openE=>x hx.
- apply:(@inner_real_norm_same_nbhs R V B hB x A).1.
  exact:(open_nbhs_nbhs (conj hOpen hx)).
- apply:(@inner_real_norm_same_nbhs R V B hB x A).2.
  exact:(open_nbhs_nbhs (conj hOpen hx)).
Qed.

(** Source for [inner_own_norm_boundary]: supporting
    the actual boundary in Federer 3.2.35,
    p. 271. The same neighbourhood filters
    identify both closure and interior, hence
    closure minus interior on every original set.
    No openness, boundedness or convexity is
    assumed for this background compatibility fact. *)
Lemma inner_own_norm_boundary (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) (A:set V):
  (@closure [the topologicalType of inner_metric_space hB] A `\`
    @interior [the topologicalType of inner_metric_space hB] A)=
  (@closure [the topologicalType of real_norm_metric_space (inner_norm_real_norm hB)] A `\`
    @interior [the topologicalType of real_norm_metric_space (inner_norm_real_norm hB)] A).
Proof.
have hClosure x:@closure [the topologicalType of inner_metric_space hB] A x <->
    @closure [the topologicalType of real_norm_metric_space (inner_norm_real_norm hB)] A x.
  split=>hx U hU.
  - exact:(hx U ((@inner_real_norm_same_nbhs R V B hB x U).2 hU)).
  - exact:(hx U ((@inner_real_norm_same_nbhs R V B hB x U).1 hU)).
apply/seteqP; split=>x [hx hOutside]; split.
- exact:(hClosure x).1 hx.
- move=>hInterior; apply:hOutside.
  exact:(@inner_real_norm_same_nbhs R V B hB x A).2 hInterior.
- exact:(hClosure x).2 hx.
- move=>hInterior; apply:hOutside.
  exact:(@inner_real_norm_same_nbhs R V B hB x A).1 hInterior.
Qed.
