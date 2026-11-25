(** Federer (1969), 3.1.20, p. 232: Phi is the family of
    coordinate neighbourhoods described in 3.1.19(4). Its union
    is open and contains B. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness NormMetric NormDifferentialUP NormRegularity NormClassZeroTopology
  InnerConvex InnerMetric InnerNormTopologyAdapters SubmanifoldChartsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [convex_coordinate_domain]: the coordinate domains
    forming Phi in the first paragraph of Federer 3.1.20, p. 232,
    with the laws of 3.1.19(4), p. 231. This predicate specifies
    chart data without selecting their implementations. *)
Definition convex_coordinate_domain (R:realType) n mu k (B:set (R_n R n)) (T:set (R_n R n)) :=
  exists (V:set (R_n R mu)) (phi:R_n R n->R_n R mu) (psi:R_n R mu->R_n R n),
    is_inner_convex V /\
    norm_class (inner_norm_real_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R mu)) T phi k /\
    norm_class (inner_norm_real_norm (@euclidean_inner_productP R mu))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) V psi k /\
    (forall x,T x -> V (phi x)) /\ psi @` V=B `&` T /\
    forall u,V u -> phi (psi u)=u.

(** Source for [convex_coordinate_domain_open]: each member of
    Phi is open, the opening construction of Federer 3.1.20,
    p. 232. Openness follows from its class-k coordinate map. *)
Lemma convex_coordinate_domain_open (R:realType) n mu k B T :
  @convex_coordinate_domain R n mu k B T ->
  @open [the topologicalType of inner_metric_space (@euclidean_inner_productP R n)] T.
Proof.
move=>[V [phi [psi [hconv [hphi hrest]]]]].
apply: (inner_norm_openP (@euclidean_inner_productP R n) T).2.
exact: norm_class_zero_domain_open (norm_class_continuous hphi).
Qed.

(** Source for [convex_coordinate_cover_contains]: B lies in
    the union of its coordinate domains Phi, Federer 3.1.20,
    p. 232, by the neighbourhood condition of 3.1.19(4). *)
Lemma convex_coordinate_cover_contains (R:realType) n mu k B :
  @has_convex_coordinate_charts R n mu k B ->
  B `<=` \bigcup_(T in (@convex_coordinate_domain R n mu k B)) T.
Proof.
move=>hB b hb.
have [T [V [phi [psi [hTb [hconv [hphi [hpsi [hphiV [hpsiT [him hcan]]]]]]]]]]]:=hB b hb.
exists T.
- exists V,phi,psi; split=>//; split=>//; split=>//; split=>//; by split.
- exact (@norm_domain_interior_member R (R_n R n)
    (inner_norm (@euclidean_inner_productP R n)) (inner_norm_real_norm (@euclidean_inner_productP R n))
    T b hTb).
Qed.
