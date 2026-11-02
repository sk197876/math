(** Federer (1969), 3.1.22, p. 236: the differential
    of a coordinate inverse identifies the parameter space with Tan(B,b). *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom TensorUP RealNormUP NormMetric NormDifferentialUP
  NormDifferentialLocal NormDifferentialChain NormDifferentialEnlarge NormDifferentialInverseIdentities
  NormCoordinateSystemUP RetractionTangentIdentity TangentConeUP TangentConeBasic TangentOpenDomain
  TangentDifferentialImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope classical_set_scope.

(** Source for [norm_coordinate_tangent_inverse]: the assertion
    Dpsi[phi(b)]:R^mu is isomorphic to Tan(B,b) in Federer
    3.1.22, p. 236. Its inverse is the restriction
    of Dphi(b). Both cancellation laws and the exact range
    are proved from the coordinate laws and tangent transport. *)
Theorem norm_coordinate_tangent_inverse (R:realType) (X Z:lmodType R)
    (NX:X->R) (NZ:Z->R) (hNX:is_real_norm NX) (hNZ:is_real_norm NZ)
    (B T:set X) (V:set Z) (phi:X->Z) (psi:Z->X) k a
    (E:Hom X Z) (J:Hom Z X) :
  is_norm_coordinate_system hNX hNZ B T V phi psi k -> B a -> T a ->
  has_norm_differential NX NZ T phi a E ->
  has_norm_differential NZ NX V psi (phi a) J ->
  cancel J E /\
  (forall v,norm_tangent_cone NX B a v -> J (E v)=v) /\
  norm_tangent_cone NX B a=range J.
Proof.
move=>hc ha ht hphi hpsi.
have hbase:=norm_coordinate_base_inverse hc ha ht.
have hpsiB u (hu:V u):B (psi u):=(norm_coordinate_backward_membership hc hu).1.
have hphib:has_norm_differential NX NZ T phi (psi (phi a)) E by rewrite hbase.
have hid:=@norm_differentials_left_inverse R Z X NZ NX hNZ hNX V T psi phi
  (phi a) J E (fun u hu=>(norm_coordinate_backward_membership hc hu).2)
  (norm_coordinate_cancel hc) hpsi hphib.
have hleft:cancel J E by move=>w; exact (congr1 (fun H:Hom Z Z=>H w) hid).
have hchain:=norm_differential_chain hNX hNZ hNX hphi hpsi.
have hmap x (hx:T x):T x /\ V (phi x) by split=>//; exact (norm_coordinate_forward_range hc hx).
have hr:=norm_differential_restrict hmap (norm_differential_interior hphi) hchain.
have hright v (hv:norm_tangent_cone NX B a v):J (E v)=v.
  exact (@norm_retraction_differential_tangent R X NX hNX B T
    (fun x=>psi (phi x)) a (hom_comp J E) ha hr
    (fun x hx ht=>norm_coordinate_base_inverse hc hx ht) v hv).
have hJT w:norm_tangent_cone NX B a (J w).
  have hw:norm_tangent_cone NZ V (phi a) w.
    by rewrite (norm_tangent_open_domain hNZ (norm_differential_interior hpsi)).
  have hi:=@norm_differential_tangent_image R Z X NZ NX hNZ hNX V V psi (phi a) J hpsi w hw.
  rewrite hbase in hi.
  apply: (@norm_tangent_mono R X NX (psi @` (V `&` V)) B a _ (J w) hi).
  by move=>x [u [hu _] <-]; exact: hpsiB hu.
split; first exact hleft.
split; first exact hright.
apply/seteqP; split=>v hv.
- exists (E v); first exact Logic.I; exact (hright v hv).
- have [w _ <-]:=hv; exact: hJT.
Qed.
