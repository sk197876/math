(** Federer (1969), 3.1.23, pp. 236–237: the
    small graph correction p*-psi, translated at the base point. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLinear
  NormDifferentialLocal NormDifferentialArithmetic NormDifferentialSubtraction NormRegularity NormRegularityOperations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [graph_defect_class]: supporting the class-k
    graph correction in Federer 3.1.23, p. 237.
    Its pointwise defining equation is supplied as a law;
    no particular graph parametrisation is chosen. *)
Lemma graph_defect_class (R:realType) (Z X:lmodType R)
    (NZ:Z->R) (NX:X->R) (hNZ:is_real_norm NZ) (hNX:is_real_norm NX)
    (V:Z->Prop) (psi G:Z->X) (J:Hom Z X) b beta k :
  (forall z,G z=J z-psi z+(b-J beta)) ->
  norm_bounded_linear NZ NX J -> norm_class hNZ hNX V psi k ->
  norm_class hNZ hNX V G k.
Proof.
move=>hG hJ hpsi.
have hopen z (hz:V z):norm_domain_interior NZ V z:=(@norm_class_continuous R Z X NZ NX hNZ hNX V psi k hpsi z hz).1.
have hj:=@norm_class_linear R Z X NZ NX hNZ hNX V J k hopen hJ.
have hc:=@norm_class_constant R Z X NZ NX hNZ hNX V (b-J beta) k hopen.
have hs:=norm_class_add (norm_class_subtract hj hpsi) hc.
exact (norm_class_domain_agreement (fun z _=>esym (hG z)) hs).
Qed.

(** Source for [graph_defect_differential]: the differential
    p*-Dpsi in Federer 3.1.23, p. 237, before
    composing with p. Translating source and target does not
    alter this differential. *)
Lemma graph_defect_differential (R:realType) (Z X:lmodType R)
    (NZ:Z->R) (NX:X->R) (hNZ:is_real_norm NZ) (hNX:is_real_norm NX)
    (V:Z->Prop) (psi G:Z->X) (J:Hom Z X) b beta z (L:Hom Z X) :
  (forall u,G u=J u-psi u+(b-J beta)) ->
  norm_bounded_linear NZ NX J -> has_norm_differential NZ NX V psi z L ->
  has_norm_differential NZ NX V G z (J-L).
Proof.
move=>hG hJ hpsi.
have hj:=@norm_differential_linear R Z X NZ NX hNZ hNX V z J
  (norm_differential_interior hpsi) hJ.
have hc:=@norm_differential_constant R Z X NZ NX hNZ hNX V z (b-J beta)
  (norm_differential_interior hpsi).
have hs:=norm_differential_add hNX (norm_differential_subtract hNZ hNX hj hpsi) hc.
rewrite addr0 in hs.
exact (norm_differential_domain_agreement hNZ (fun u _=>esym (hG u)) hs).
Qed.

(** Source for [graph_defect_base_zero]: the correction vanishes
    at the base parameter in Federer 3.1.23, pp. 236–237,
    using psi[p(b)]=b; the book normalizes both points to zero. *)
Lemma graph_defect_base_zero (R:fieldType) (Z X:lmodType R)
    (psi G:Z->X) (J:Hom Z X) b beta :
  (forall z,G z=J z-psi z+(b-J beta)) -> psi beta=b -> G beta=0.
Proof. move=>hG hb; by rewrite hG hb addrA subrK subrr. Qed.
