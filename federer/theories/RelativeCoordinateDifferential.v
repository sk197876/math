(** Federer (1969), 3.1.22, pp. 235–236: relative
    differentiation is equivalent to differentiation in any coordinate system. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormDifferentialLocal
  NormDifferentialChain NormDifferentialEnlarge NormCoordinateSystemUP NormCoordinateTangent
  TangentConeUP PartialFunctionUP RelativeDifferentialUP ParametricDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [relative_coordinate_differential_criterion]: conditions
    (1), (3) and [3] in Federer 3.1.22, pp. 235–236.
    For every actual coordinate system and its actual derivatives,
    the exact relative graph is equivalent to the coordinate derivative
    transported through Dpsi. The proof uses the two local agreements
    and chain rule printed on p. 236. *)
Theorem relative_coordinate_differential_criterion (R:realType) (X Z Y:lmodType R)
    (NX:X->R) (NZ:Z->R) (NY:Y->R)
    (hNX:is_real_norm NX) (hNZ:is_real_norm NZ) (hNY:is_real_norm NY)
    (A B T:set X) (V:set Z) (phi:X->Z) (psi:Z->X) (f:X->Y)
    a (E:Hom X Z) (J:Hom Z X) (L:partial_function X Y) :
  is_norm_coordinate_system hNX hNZ B T V phi psi 1%N ->
  B a -> T a -> B `<=` A ->
  has_norm_differential NX NZ T phi a E ->
  has_norm_differential NZ NX V psi (phi a) J ->
  (@has_relative_norm_differential R X Y NX NY hNX A B f a L <->
    exists Q:Hom Z Y,has_norm_differential NZ NY V (fun u=>f (psi u)) (phi a) Q /\
      is_parametric_differential_restriction J Q L).
Proof.
move=>hc ha ht hBA hphi hpsi.
have hbase:=norm_coordinate_base_inverse hc ha ht.
have [hleft [hright hTan]]:=norm_coordinate_tangent_inverse hc ha ht hphi hpsi.
split.
- move=>[hcl [U [g [D [hg [hfg hDL]]]]]].
  have hg':has_norm_differential NX NY U g (psi (phi a)) D by rewrite hbase.
  have hcomp:=norm_differential_chain hNZ hNX hNY hpsi hg'.
  have heq u (hu:V u /\ U (psi u)):g (psi u)=f (psi u).
    symmetry; exact (hfg (psi u) (norm_coordinate_backward_membership hc hu.1).1 hu.2).2.
  have hfcomp:=norm_differential_domain_agreement hNZ heq hcomp.
  have hfd:=@norm_differential_enlarge R Z Y NZ NY
    (fun u=>V u /\ U (psi u)) V (fun u=>f (psi u)) (phi a)
    (hom_comp D J) (fun u hu=>hu.1) hfcomp.
  exists (hom_comp D J); split; first exact hfd.
  move=>v y; split.
  + move=>hy; have [hv he]:=(hDL v y).1 hy.
    rewrite hTan in hv; have [w _ hw]:=hv.
    exists w; split=>//; by rewrite hom_compE hw.
  + move=>[w [hw hQ]]; apply: (hDL v y).2; split.
    * rewrite hTan; exists w; first exact Logic.I; exact hw.
    * move: hQ; by rewrite hom_compE hw.
- move=>[Q [hQ hL]]; split; first exact: subset_closure ha.
  have hcomp:=norm_differential_chain hNX hNZ hNY hphi hQ.
  have hmap x (hx:T x):T x /\ V (phi x) by split=>//; exact (norm_coordinate_forward_range hc hx).
  have hd:=norm_differential_restrict hmap (norm_differential_interior hphi) hcomp.
  exists T,(fun x=>f (psi (phi x))),(hom_comp Q E); split; first exact hd.
  split.
  + move=>x hx hxT; split; first exact (hBA x hx).
    by rewrite (norm_coordinate_base_inverse hc hx hxT).
  + move=>v y; split.
    * move=>hy; have [w [hw hQw]]:=(hL v y).1 hy; split.
      -- rewrite hTan; exists w; first exact Logic.I; exact hw.
      -- by rewrite hom_compE -hw hleft.
    * move=>[hv hQv]; apply: (hL v y).2; exists (E v); split.
      -- exact (hright v hv).
      -- exact hQv.
Qed.
