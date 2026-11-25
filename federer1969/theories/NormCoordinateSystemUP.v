(** Federer (1969), 3.1.19, p. 231, coordinate-system
    paragraph, as used in 3.1.22, pp. 235–236. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import RealNormUP NormRegularity NormCoordinateTopology RetractionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_norm_coordinate_system]: abstract laws of phi
    and its inverse psi in Federer 3.1.19(4), p. 231,
    used by 3.1.22, pp. 235–236. These laws also make
    sense in arbitrary normed spaces and do not require convexity
    of the open parameter domain. The Euclidean existence theorem
    supplies them; the record introduces no existence axiom. *)
Record is_norm_coordinate_system (R:realType) (X Z:lmodType R)
    (NX:X->R) (NZ:Z->R) (hNX:is_real_norm NX) (hNZ:is_real_norm NZ)
    (B T:set X) (V:set Z) (phi:X->Z) (psi:Z->X) k : Prop := {
  (** Source for [norm_coordinate_class_forward]: class k of phi,
      Federer 3.1.19(4), p. 231, used in 3.1.22, p. 236. *)
  norm_coordinate_class_forward:norm_class hNX hNZ T phi k;
  (** Source for [norm_coordinate_class_backward]: class k of psi,
      Federer 3.1.19(4), p. 231, used in 3.1.22, p. 236. *)
  norm_coordinate_class_backward:norm_class hNZ hNX V psi k;
  (** Source for [norm_coordinate_forward_range]: phi maps T into V,
      Federer 3.1.19(4), p. 231, used in 3.1.22, p. 236. *)
  norm_coordinate_forward_range:forall x,T x -> V (phi x);
  (** Source for [norm_coordinate_image]: psi(V)=B intersect T,
      Federer 3.1.19(4), p. 231, used in 3.1.22, p. 236. *)
  norm_coordinate_image:psi @` V=B `&` T;
  (** Source for [norm_coordinate_cancel]: phi psi is identity on V,
      Federer 3.1.19(4), p. 231, used in 3.1.22, p. 236. *)
  norm_coordinate_cancel:forall u,V u -> phi (psi u)=u
}.

(** Source for [norm_coordinate_base_inverse]: psi phi is identity
    on B intersect T, in Federer 3.1.19, p. 231,
    supporting every local agreement in 3.1.22, p. 236. *)
Lemma norm_coordinate_base_inverse (R:realType) (X Z:lmodType R)
    (NX:X->R) (NZ:Z->R) (hNX:is_real_norm NX) (hNZ:is_real_norm NZ)
    (B T:set X) (V:set Z) (phi:X->Z) (psi:Z->X) k :
  is_norm_coordinate_system hNX hNZ B T V phi psi k ->
  forall a,B a -> T a -> psi (phi a)=a.
Proof.
move=>hc a ha ht.
exact (@norm_coordinate_inverse R X Z (B `&` T) V phi psi
  (norm_coordinate_image hc) (norm_coordinate_cancel hc) a (conj ha ht)).
Qed.

(** Source for [norm_coordinate_backward_membership]: psi takes
    V into B intersect T, the image identity of Federer
    3.1.19(4), p. 231, used in 3.1.22, p. 236. *)
Lemma norm_coordinate_backward_membership (R:realType) (X Z:lmodType R)
    (NX:X->R) (NZ:Z->R) (hNX:is_real_norm NX) (hNZ:is_real_norm NZ)
    (B T:set X) (V:set Z) (phi:X->Z) (psi:Z->X) k :
  is_norm_coordinate_system hNX hNZ B T V phi psi k ->
  forall u,V u -> B (psi u) /\ T (psi u).
Proof.
move=>hc u hu; have hi:(psi @` V) (psi u) by exists u.
by rewrite (norm_coordinate_image hc) in hi.
Qed.

(** Source for [norm_coordinate_system_retraction]: psi phi is
    the local class-k retraction in Federer 3.1.19, p. 231,
    used in the proof of 3.1.22, p. 236. *)
Lemma norm_coordinate_system_retraction (R:realType) (X Z:lmodType R)
    (NX:X->R) (NZ:Z->R) (hNX:is_real_norm NX) (hNZ:is_real_norm NZ)
    (B T:set X) (V:set Z) (phi:X->Z) (psi:Z->X) k :
  is_norm_coordinate_system hNX hNZ B T V phi psi k ->
  is_norm_class_retraction hNX T (B `&` T) (fun x=>psi (phi x)) k.
Proof.
move=>hc.
exact (@norm_coordinate_retraction R X Z NX NZ hNX hNZ T (B `&` T) V phi psi k
  (norm_coordinate_class_forward hc) (norm_coordinate_class_backward hc)
  (fun x hx=>hx.2) (norm_coordinate_forward_range hc)
  (norm_coordinate_image hc) (norm_coordinate_cancel hc)).
Qed.
