(** Federer (1969), 3.3.4, p. 288: the proof assumes
    the centre does not belong to A. Prove the reduction by
    removing only that point, preserving the original cone masses
    and the original punctured affine-fibre accumulation property. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets functions reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations GrassmannSubspaces ModuleQuotient
  EuclideanInnerProduct InnerMetric StructureCone StructureConeBasic
  ExtendedRealBounds StructurePlaneGrowth PositiveRadiusLimitCongruence PositiveRightOrderLimit
  SuslinSetUP BorelSuslinImages BorelClosedProjection TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_remove_excluded_vertex_intersection]:
    supporting the initial point-removal reduction of
    Federer 3.3.4, p. 288. Removing a point already
    excluded by a test set does not change its intersection. *)
Lemma structure_remove_excluded_vertex_intersection (X:Type)
    (A C:set X) (a:X):~C a ->(A `\` [set a]) `&` C=A `&` C.
Proof.
move=>hNot; apply/seteqP; split=>x.
- by move=>[[hA _] hC].
- move=>[hA hC]; split=>//; split=>// he.
  change (x=a) in he; subst x; exact:(hNot hC).
Qed.

(** Source for [structure_cone_remove_vertex]: the exact
    cone-mass preservation underlying the assumption a not
    in A in Federer 3.3.4, p. 288. Every cone
    excludes its own vertex by its original strict inequality. *)
Lemma structure_cone_remove_vertex (R:realType) n k
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (V:G (R_n R n) k) a (r: \bar R) (s:R):
  (A `\` [set a]) `&` structure_cone V a r s=A `&` structure_cone V a r s.
Proof.
apply:structure_remove_excluded_vertex_intersection.
exact:(@structure_cone_vertex_excluded R n k V a r s).
Qed.

(** Source for [structure_plane_radial_remove_vertex]: the
    actual radius suprema in alternatives (1) and (2)
    of Federer 3.3.4, p. 288, are unchanged when
    the centre alone is removed from the original A. *)
Lemma structure_plane_radial_remove_vertex (R:realType) n k m
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    a (V:G (R_n R n) k) (delta s:R):
  structure_plane_radial_supremum m phi (A `\` [set a]) a V delta s=
  structure_plane_radial_supremum m phi A a V delta s.
Proof.
rewrite /structure_plane_radial_supremum; congr (extended_real_sup _).
apply/seteqP; split=>v [r [hr ->]]; exists r=>//; split=>//;
  by rewrite structure_cone_remove_vertex.
Qed.

(** Source for [structure_plane_accumulation_remove_vertex]:
    alternative (3) in Federer 3.3.4, p. 288,
    already uses the punctured original fibre, so removing
    its centre from A leaves the closure condition unchanged. *)
Lemma structure_plane_accumulation_remove_vertex (R:realType) n k
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    a (V:G (R_n R n) k):
  structure_plane_accumulation (A `\` [set a]) a V <->
  structure_plane_accumulation A a V.
Proof.
have he:[set x:inner_metric_space (@euclidean_inner_productP R n)|
    (A `\` [set a]) x /\ x!=a /\ grassmann_val V (x-a)]=
    [set x:inner_metric_space (@euclidean_inner_productP R n)|
    A x /\ x!=a /\ grassmann_val V (x-a)].
  apply/seteqP; split=>x.
  - by move=>[[hA _] hRest].
  - move=>[hA [hNe hV]]; split; last by split.
    split=>// he; change (x=a) in he; subst x; by rewrite eqxx in hNe.
by rewrite /structure_plane_accumulation he.
Qed.

(** Source for [structure_punctured_source_suslin]: the
    point-removal reduction of Federer 3.3.4, p. 288,
    preserves the original Suslin hypothesis. The complement
    of the singleton is open in the original Euclidean metric. *)
Lemma structure_punctured_source_suslin (R:realType) n
    (A:set (inner_metric_space (@euclidean_inner_productP R n))) a:
  is_suslin_set R A ->is_suslin_set R (A `\` [set a]).
Proof.
move=>hA; rewrite setDE; apply:suslin_binary_intersection=>//.
apply:metric_borel_suslin; apply:open_borel_set; apply:closed_openC.
apply:accessible_closed_set1; apply:hausdorff_accessible; exact:metric_hausdorff.
Qed.
