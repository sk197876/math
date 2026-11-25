(** Supporting Federer (1969), 3.4.8(1),(5),
    pp. 326, 328: actual affine coordinate germs.
    A bounded functional composed with translation is
    analytic by 3.1.24, p. 240. The construction
    serves only to prove existence of representatives. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws NormAnalyticUP
  NormAnalyticLinear NormAnalyticTranslation NormAnalyticOperations
  AnalyticGermRepresentatives.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [pointed_functional_representative_exists]:
    the original linear coordinate shifted to an
    arbitrary centre has an actual analytic representative,
    supporting 3.4.8(1),(5), pp. 326, 328.
    The original coordinates themselves use centre zero. *)
Theorem pointed_functional_representative_exists (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) a (xi:Hom X R^o):
  norm_bounded_linear NX (fun z:R^o=>`|z|) xi ->
  exists f:@analytic_representative_type R X NX hNX a,
    forall x,analytic_representative_value f x = xi (x-a).
Proof.
move=>hXi.
pose NS:=fun z:R^o=>`|z|.
pose hNS:=@scalar_absolute_value_norm R.
have hLinear:=@norm_bounded_linear_analytic R X R^o NX NS hNX hNS setT
  (fun x hx=>norm_full_domain_interior NX x) xi hXi.
have hTranslate:=(@norm_translations_analytic R X NX hNX setT
  (fun x hx=>norm_full_domain_interior NX x) a).2.
have hCompose:=@norm_analytic_compose_on R X X R^o NX NX NS hNX hNX hNS setT setT
  (fun x=>x-a) xi (fun x hx=>Logic.I) hTranslate hLinear.
have [f hF]:=@analytic_representative_from_domain R X NX hNX a setT
  (fun x=>xi (x-a)) (hCompose a Logic.I).
exists f=>x;exact:(congr1 (fun g:X->R=>g x) hF).
Qed.
