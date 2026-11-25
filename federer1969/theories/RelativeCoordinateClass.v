(** Federer (1969), 3.1.22, p. 236, final paragraph:
    class k relative to a submanifold is class k in coordinates. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import RealNormUP NormRegularity NormRegularityOperations NormRegularityLocal
  NormCoordinateSystemUP RelativeClassUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [relative_class_in_coordinates]: the forward
    implication of the last paragraph of Federer 3.1.22,
    p. 236. Every coordinate inverse psi takes the local
    ambient extensions to local representatives of f composed with psi.
    Locality then gives class k on the whole parameter domain. *)
Theorem relative_class_in_coordinates (R:realType) (X Z Y:lmodType R)
    (NX:X->R) (NZ:Z->R) (NY:Y->R)
    (hNX:is_real_norm NX) (hNZ:is_real_norm NZ) (hNY:is_real_norm NY)
    (A B T:set X) (V:set Z) (phi:X->Z) (psi:Z->X) (f:X->Y) k :
  is_norm_coordinate_system hNX hNZ B T V phi psi k ->
  @norm_class_relative R X Y NX NY hNX hNY A B f k ->
  norm_class hNZ hNY V (fun z=>f (psi z)) k.
Proof.
move=>hc hf.
apply: norm_class_local_representatives=>z hz.
have hb: B (psi z):=(norm_coordinate_backward_membership hc hz).1.
have [U [g [hU [hg hag]]]]:=hf (psi z) hb.
pose O:=fun u=>V u /\ U (psi u).
exists O,(fun u=>g (psi u)); split; first by split.
split; first by move=>u hu; exact hu.1.
split; first exact (norm_class_composition (norm_coordinate_class_backward hc) hg).
move=>u [hu hv]; symmetry.
exact (hag (psi u) (norm_coordinate_backward_membership hc hu).1 hv).2.
Qed.

(** Source for [coordinate_class_relative_local_extension]: the
    reverse implication of the final paragraph of Federer 3.1.22,
    p. 236. A class-k coordinate representative extends to
    the ambient neighbourhood as (f composed with psi) composed
    with phi. This is the actual local extension, with exact agreement. *)
Lemma coordinate_class_relative_local_extension (R:realType) (X Z Y:lmodType R)
    (NX:X->R) (NZ:Z->R) (NY:Y->R)
    (hNX:is_real_norm NX) (hNZ:is_real_norm NZ) (hNY:is_real_norm NY)
    (A B T:set X) (V:set Z) (phi:X->Z) (psi:Z->X) (f:X->Y) k :
  is_norm_coordinate_system hNX hNZ B T V phi psi k -> B `<=` A ->
  norm_class hNZ hNY V (fun z=>f (psi z)) k ->
  exists g,norm_class hNX hNY T g k /\
    forall x,B x -> T x -> A x /\ f x=g x.
Proof.
move=>hc hBA hf.
exists (fun x=>f (psi (phi x))); split.
- exact (norm_class_compose_on (norm_coordinate_forward_range hc)
    (norm_coordinate_class_forward hc) hf).
- move=>x hx ht; split; first exact (hBA x hx).
  by rewrite (norm_coordinate_base_inverse hc hx ht).
Qed.
