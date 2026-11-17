(** Federer (1969), 3.4.7, p. 325: the
    preparation multiplier is a unit because its value at
    the origin is nonzero. The actual local reciprocal
    proves this assertion for every normed source. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormAnalyticUP NormAnalyticDomain
  NormAnalyticComposition NormAnalyticLocal ScalarReciprocalAnalytic LocalGermUP LocalGermSealed
  AnalyticGermNeighbourhood AnalyticGermRepresentatives AnalyticGermUP AnalyticGermSealed
  AnalyticGermRingLaws AnalyticGermRing CommutativeFactorizationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_germ_unit_iff_nonzero_value]:
    the unit assertion used in 3.4.7, p. 325.
    A germ is a unit exactly when any original analytic
    representative has nonzero value at the centre. No
    reciprocal germ is supplied as an extra hypothesis. *)
Theorem analytic_germ_unit_iff_nonzero_value (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) a
    (f:@analytic_representative_type R X NX hNX a):
  is_commutative_unit (analytic_germ f:@analytic_germ_ring R X NX hNX a) <->
  analytic_representative_value f a<>0.
Proof.
pose G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX a)].
pose P:=@analytic_representative_type R X NX hNX a.
pose value:=@analytic_representative_value R X NX hNX a.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
pose oneP:=@analytic_constant_representative R X NX hNX a 1.
split.
- move=>[beta hUnit] hZero.
  have [g hg]:=@analytic_germ_has_representative R X NX hNX a beta.
  have hEqual:analytic_germ (@analytic_multiply_representatives R X NX hNX a g f) =
      analytic_germ oneP.
    rewrite -(@analytic_germ_multiply_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R X NX hNX a)) hg.
    exact:hUnit.
  have hCentre:=analytic_germ_equal_at_centre hEqual.
  change (analytic_representative_value g a*analytic_representative_value f a = 1) in hCentre.
  rewrite hZero mulr0 in hCentre.
  have h01:(0:R)!=1 by rewrite eq_sym oner_eq0.
  by rewrite hCentre eqxx in h01.
- move=>hNonzero.
  have [U [haU [hUT [hU hF]]]]:=analytic_germ_open_representative (analytic_representative_analytic f).
  pose C:set X:=fun x=>U x /\value f x!=0.
  have haC:C a by split;last exact/eqP.
  have hInverse:=@norm_analytic_composition R X R^o R^o NX (fun t=>`|t|) (fun t=>`|t|)
    hNX (@scalar_absolute_value_norm R) (@scalar_absolute_value_norm R)
    U [set t:R^o|t!=0] (value f) (fun t=>t^-1) hF (@scalar_reciprocal_analytic R).
  have [g hG]:=@analytic_representative_from_domain R X NX hNX a C
    (fun x=>(value f x)^-1) (hInverse a haC).
  exists (analytic_germ g:G).
  change (@AnalyticGerms.mul R X NX hNX a (analytic_germ g) (analytic_germ f) = analytic_germ oneP).
  rewrite (@analytic_germ_multiply_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R X NX hNX a)).
  apply/(local_germ_equality (@LocalGerms.laws T R P value a)).
  exists C;split.
  + exact:(norm_analytic_domain_open hInverse).
  + split;first exact:haC.
    move=>x hx;change (analytic_representative_value g x*analytic_representative_value f x = 1).
    rewrite hG;exact:mulVf hx.2.
Qed.
