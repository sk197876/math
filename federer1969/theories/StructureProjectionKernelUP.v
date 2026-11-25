(** Federer (1969), 3.3.1, p. 287: the map from O*(n,m)
    to G(n,n-m) associates to p its actual kernel. Specify this
    object by membership before constructing or topologizing it. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import GrassmannAbbreviations GrassmannSubspaces ModuleQuotient
  EuclideanProjectionSpace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_structure_projection_kernel]: the last sentence
    of Federer 3.3.1, p. 287, in words: the associated (n-m)-plane
    consists exactly of the vectors annihilated by the original p.
    No continuity, openness or measure assertion is part of these laws. *)
Definition is_structure_projection_kernel (R:realType) n m
    (p:euclidean_projection_space R n m) (K:G (R_n R n) (n-m)):Prop:=
  forall x,grassmann_val K x <->euclidean_projection_linear p x=0.
