(** Opaque public cone object for Federer (1969), 3.3.1, p. 287.
    Its existence construction is hidden; only the independently
    stated membership laws are exposed. *)
From mathcomp Require Import all_boot boolp classical_sets reals constructive_ereal.
From Federer Require Import GrassmannAbbreviations GrassmannSubspaces
  EuclideanInnerProduct InnerMetric StructureConeUP StructureConeConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type StructureConeSignature.
(** Source for [value]: X(a,r,V,s), the cone of Federer
    3.3.1, p. 287, specified before the existence proof. *)
Parameter value:forall (R:realType) n k (V:G (R_n R n) k)
  (a:inner_metric_space (@euclidean_inner_productP R n)) (r: \bar R) (s:R),
  set (inner_metric_space (@euclidean_inner_productP R n)).
(** Source for [laws]: the exact membership specification of
    X(a,r,V,s), Federer 3.3.1, p. 287. *)
Parameter laws:forall (R:realType) n k (V:G (R_n R n) k)
  (a:inner_metric_space (@euclidean_inner_productP R n)) (r: \bar R) (s:R),
  is_structure_cone V a r s (@value R n k V a r s).
End StructureConeSignature.

Module StructureCone:StructureConeSignature.
(** Source for [value]: private realization of the proved cone
    existence theorem for Federer 3.3.1, p. 287. *)
Definition value (R:realType) n k (V:G (R_n R n) k)
    (a:inner_metric_space (@euclidean_inner_productP R n)) (r: \bar R) (s:R):=
  projT1 (cid (structure_cone_exists V a r s)).
(** Source for [laws]: the selected cone satisfies the independent
    specification of Federer 3.3.1, p. 287. *)
Lemma laws (R:realType) n k (V:G (R_n R n) k)
    (a:inner_metric_space (@euclidean_inner_productP R n)) (r: \bar R) (s:R):
  is_structure_cone V a r s (@value R n k V a r s).
Proof. exact:projT2 (cid (structure_cone_exists V a r s)). Qed.
End StructureCone.
