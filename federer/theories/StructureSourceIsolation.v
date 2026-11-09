(** Federer (1969), 3.3.4, p. 288: the absence of
    punctured source accumulation gives an actual positive
    source-free punctured neighbourhood. This general metric
    reduction is used at the zero-degree endpoint. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerNorm
  GrassmannAbbreviations GrassmannSubspaces ModuleQuotient
  StructurePlaneGrowth StructureExtremePlanes.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_no_source_accumulation_isolated]:
    supporting local alternative for Federer 3.3.4,
    p. 288: if a is not an accumulation point
    of the original punctured source, some positive
    neighbourhood contains no such source point. *)
Theorem structure_no_source_accumulation_isolated (R:realType) n
    (A:set (inner_metric_space (@euclidean_inner_productP R n))) a:
  ~closure [set x:inner_metric_space (@euclidean_inner_productP R n)|A x /\ x!=a] a ->
  exists delta:R,0<delta /\ forall x,A x ->
    0<inner_norm (@euclidean_inner_productP R n) (x-a)<delta ->False.
Proof.
move=>hNot; apply:contrapT=>hNo; apply:hNot=>U hU.
have [e he hBall]:=proj1 (metricType_numDomainType.nbhs_mdistP a U) hU.
have hExists:exists x,A x /\ 0<inner_norm (@euclidean_inner_productP R n) (x-a)<e.
  apply:contrapT=>hNone; apply:hNo; exists e; split=>// x hx hNear.
  apply:hNone; by exists x.
have [x [hx hNear]]:=hExists.
exists x; split.
- split=>//; by move:(andP hNear).1; rewrite inner_norm_gt0 subr_eq0.
- apply:hBall; change (is_true (mdist a x<e)).
  rewrite inner_metric_distanceE -[a-x]opprB inner_normN; exact:(andP hNear).2.
Qed.

(** Source for [structure_full_plane_accumulation]: the
    full-plane endpoint of alternative (3) in Federer
    3.3.4, p. 288, is exactly punctured source
    accumulation; it introduces no projection or measure premise. *)
Lemma structure_full_plane_accumulation (R:realType) n
    (A:set (inner_metric_space (@euclidean_inner_productP R n))) a
    (V:G (R_n R n) n):
  structure_plane_accumulation A a V <->
  closure [set x:inner_metric_space (@euclidean_inner_productP R n)|A x /\ x!=a] a.
Proof.
have he:[set x:inner_metric_space (@euclidean_inner_productP R n)|
    A x /\ x!=a /\ grassmann_val V (x-a)]=[set x|A x /\ x!=a].
  apply/seteqP; split=>x; first by move=>[hx [hne _]].
  move=>[hx hne]; split=>//; split=>//; exact:structure_full_plane_member.
by rewrite /structure_plane_accumulation he.
Qed.
