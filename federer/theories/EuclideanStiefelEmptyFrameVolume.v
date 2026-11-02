(** Federer (1969), 3.2.28(5), p. 267:
    the empty-frame boundary supporting the volume
    induction. The printed induction starts with
    O(n,1); its zero-frame extension has unit H^0 mass. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanHomInnerCharts
  OrthogonalMaps EuclideanManifoldVolumes HausdorffCountingMeasure CountingInjectionBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_stiefel_empty_frame_volume]:
    auxiliary degree-zero base for the recurrence of
    Federer 3.2.28(3),(5), pp. 266–267.
    There is exactly one map from the zero space,
    and its H^0 mass is one. This does not
    assert a factor-two orientation law at m=0. *)
Theorem euclidean_stiefel_empty_frame_volume (R:realType) n:
  euclidean_stiefel_volume R n 0= 1%E.
Proof.
have hVec (x:R_n R 0):x=0.
  apply/ffunP=>i; exfalso.
  have hi:=ltn_ord i; by move:hi; rewrite ltn0.
have hHom (f:Hom (R_n R 0) (R_n R n)):f=0.
  apply:hom_ext=>x; by rewrite (hVec x) linear0 ?hom_zeroE.
have hZero:is_orthogonal_map (@euclidean_inner_product R 0) (@euclidean_inner_product R n)
    (hom_as_linear (0:Hom (R_n R 0) (R_n R n))).
  move=>x y.
  change (euclidean_inner_product ((0:Hom (R_n R 0) (R_n R n)) x)
    ((0:Hom (R_n R 0) (R_n R n)) y)=euclidean_inner_product x y).
  rewrite !hom_zeroE /euclidean_inner_product big_ord0.
  apply:big1=>i _; by rewrite !ffunE mul0r.
have hSet:[set f:Hom (R_n R 0) (R_n R n)|is_orthogonal_map (@euclidean_inner_product R 0)
    (@euclidean_inner_product R n) (hom_as_linear f)]=[set 0].
  apply/seteqP; split=>f.
  - move=>_; exact:hHom.
  - move=>->; exact hZero.
rewrite /euclidean_stiefel_volume mul0n div0n hausdorff_zero_counting_measure hSet.
exact:counting_measure_singleton_value.
Qed.
