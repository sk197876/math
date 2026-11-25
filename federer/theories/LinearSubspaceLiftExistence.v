(** Federer (1969), 4.1.1, pp. 344–345: corestrict a linear
    map whose values lie in a specified subspace. This supporting
    existence proof reuses the project's algebraic retraction
    theorem; no continuity of that auxiliary retraction is claimed. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Hom LinearRetraction ModuleQuotient LinearSubspaceRepresentationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [linear_subspace_lift_exists]: the linear map
    between the actual subspaces exists with unchanged values,
    supporting their inclusions in Federer 4.1.1, pp. 344–345. *)
Theorem linear_subspace_lift_exists (K:fieldType) (E W V:lmodType K)
    (S:subspace V) (inc:Hom W V) :
  is_linear_subspace_representation S inc ->
  forall L:Hom E V,(forall x,S (L x)) ->
    exists M:Hom E W,forall x,inc (M x)=L x.
Proof.
move=>hW L hL.
pose r:=hom_of_linear (linear_retraction (i:=hom_as_linear inc)
  (subspace_representation_injective hW)).
have hRet:cancel inc r.
  exact:(@linear_retractionK K W V (hom_as_linear inc)
    (subspace_representation_injective hW)).
exists (hom_comp r L)=>x.
have [w hw]:=subspace_representation_full hW (hL x).
by rewrite hom_compE -hw hRet.
Qed.
