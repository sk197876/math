(** Federer (1969), 3.4.12, p. 339, extending 3.4.7,
    p. 325: units in the actual holomorphic germ ring are
    precisely the germs with nonzero value at the centre.
    The actual local reciprocal supplies the inverse. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm
  NormMetric NormAnalyticDomain NormAnalyticLocal LocalGermUP LocalGermSealed HolomorphicReciprocal
  HolomorphicGermRepresentatives HolomorphicGermArithmeticRepresentatives HolomorphicGermUP
  HolomorphicGermOperationsUP HolomorphicGermSealed HolomorphicGermRingLaws HolomorphicGermRing
  CommutativeFactorizationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_germ_unit_iff_nonzero_value]: the original
    unit criterion used in complex preparation and factorization,
    extending 3.4.7, p. 325. No reciprocal germ or
    inverse equation is supplied as an additional hypothesis. *)
Theorem holomorphic_germ_unit_iff_nonzero_value (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:restricted_space (ComplexScalars.embed R) X->R) (hNX:is_real_norm NX) a
    (f:@holomorphic_representative_type R X NX hNX a):
  is_commutative_unit (holomorphic_germ f:@holomorphic_germ_ring R X NX hNX a) <->
  holomorphic_representative_value f a<>0.
Proof.
pose C:=ComplexScalars.C R.
pose G:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)].
pose P:=@holomorphic_representative_type R X NX hNX a.
pose value:=@holomorphic_representative_value R X NX hNX a.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
pose oneP:=@holomorphic_constant_representative R X NX hNX a 1.
split.
- move=>[beta hUnit] hZero.
  have [g hg]:=@holomorphic_germ_has_representative R X NX hNX a beta.
  have hEqual:holomorphic_germ (@holomorphic_multiply_representatives R X NX hNX a g f)=holomorphic_germ oneP.
    rewrite -(@holomorphic_germ_multiply_equation _ _ _ _ _ _ _ _ (@HolomorphicGerms.laws R X NX hNX a)) hg.
    exact:hUnit.
  have hCentre:=holomorphic_germ_equal_at_centre hEqual.
  change (holomorphic_representative_value g a*holomorphic_representative_value f a = 1) in hCentre.
  rewrite hZero mulr0 in hCentre.
  have h01:(0:C)!=1 by rewrite eq_sym oner_eq0.
  by rewrite hCentre eqxx in h01.
- move=>hNonzero.
  have [U [haU hF]]:=holomorphic_representative_holomorphic f.
  pose B:set X:=fun x=>U x /\value f x!=0.
  have haB:B a by split;last exact/eqP.
  have hInverse:=holomorphic_reciprocal hF.
  have [g hG]:=@holomorphic_representative_from_domain R X NX hNX a B
    (fun x=>(value f x)^-1) haB hInverse.
  exists (holomorphic_germ g:G).
  change (@HolomorphicGerms.mul R X NX hNX a (holomorphic_germ g) (holomorphic_germ f)=holomorphic_germ oneP).
  rewrite (@holomorphic_germ_multiply_equation _ _ _ _ _ _ _ _ (@HolomorphicGerms.laws R X NX hNX a)).
  apply/(local_germ_equality (@LocalGerms.laws T C P value a)).
  exists B;split;first exact:(norm_analytic_domain_open hInverse.1).
  split;first exact:haB.
  move=>x hx;change (holomorphic_representative_value g x*holomorphic_representative_value f x = 1).
  rewrite hG;exact:mulVf hx.2.
Qed.
