(** Federer (1969), 3.4.7, p. 325: the
    divided directional derivatives restrict to actual
    transverse analytic coefficients in the finite remainder
    module. This supporting proof retains the actual inclusion
    and projection of the opaque transverse space. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  NormAnalyticUP NormAnalyticLinear NormAnalyticComposition AnalyticGermRepresentatives
  WeierstrassTransverseUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [transverse_analytic_coefficient_representative]:
    the coefficients belong to the transverse analytic
    germ ring used in 3.4.7, p. 325.
    Their representatives are the actual divided fields
    composed with the original kernel inclusion. *)
Theorem transverse_analytic_coefficient_representative (R:realType) (X K:lmodType R)
    (NX:X->R) (NK:K->R) (hNX:is_real_norm NX) (hNK:is_real_norm NK)
    (v:X) (xi:Hom X R^o) (inclusion:Hom K X) (projection:Hom X K) (C:X->R):
  is_weierstrass_transverse_space NX NK v xi inclusion projection ->
  @norm_analytic_at R X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R)
    setT C 0 ->
  exists c:@analytic_representative_type R K NK hNK (projection 0),
    forall z,analytic_representative_value c z = C (inclusion z).
Proof.
move=>hSplit hC.
have hInclusion:=@norm_bounded_linear_analytic R K X NK NX hNK hNX setT
  (fun z _=>norm_full_domain_interior NK z) inclusion
  (weierstrass_transverse_inclusion_bounded hSplit).
have hOuter:@norm_analytic_at R X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R)
    setT C (inclusion (projection 0)).
  by rewrite !linear0.
have hComposite:=@norm_analytic_at_composition R K X R^o NK NX (fun t=>`|t|)
  hNK hNX (@scalar_absolute_value_norm R) setT setT inclusion C (projection 0)
  (hInclusion (projection 0) Logic.I) hOuter.
have [c hValues]:=@analytic_representative_from_domain R K NK hNK (projection 0)
  (fun z=>setT z /\setT (inclusion z)) (fun z=>C (inclusion z)) hComposite.
exists c=>z;by rewrite hValues.
Qed.
