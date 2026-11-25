(** Public X(a,r,V,s) of Federer (1969), 3.3.1, p. 287.
    All subsequent statements use the opaque membership laws. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal.
From Federer Require Import GrassmannAbbreviations GrassmannSubspaces
  EuclideanInnerProduct InnerMetric StructureConeUP StructureConeSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [structure_cone]: the actual cone X(a,r,V,s)
    defined in Federer 3.3.1, p. 287. Its implementation is sealed. *)
Definition structure_cone (R:realType) n k (V:G (R_n R n) k)
    (a:inner_metric_space (@euclidean_inner_productP R n)) (r: \bar R) (s:R):=
  @StructureCone.value R n k V a r s.

(** Source for [structure_cone_specification]: the displayed
    definition of X in Federer 3.3.1, p. 287, with every realization
    of distance to the original plane satisfying the infimum laws. *)
Lemma structure_cone_specification (R:realType) n k (V:G (R_n R n) k)
    (a:inner_metric_space (@euclidean_inner_productP R n)) (r: \bar R) (s:R):
  is_structure_cone V a r s (structure_cone V a r s).
Proof. exact:StructureCone.laws. Qed.
