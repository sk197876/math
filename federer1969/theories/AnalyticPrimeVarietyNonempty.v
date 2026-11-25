(** Federer (1969), 3.4.8(10), pp. 332–333:
    the original remainder germ is nonempty
    when the ideal equals its variety's
    vanishing ideal. Reuse ideal containment
    in ideal(var K) and the Boolean germ laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric AnalyticGermRing CommutativeIdealUP
  SetGermUP SetGermSealed SetGermLaws IdealVarietyGermSealed GermVanishingSealed IdealVarietyVanishingLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [analytic_variety_remainder_nonempty]:
    if gamma_0(Z) were empty, then
    var(I_g)=var(J), while an element
    of J outside I_g would vanish
    on var(I_g), 3.4.8(10),
    pp. 332–333. This is exactly
    the original contradiction argument. *)
Theorem analytic_variety_remainder_nonempty (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) a
    (I K:set [the comNzRingType of (@analytic_germ_ring R X NX hNX a)])
    (hI:is_finitely_generated_commutative_ideal I) (hK:is_finitely_generated_commutative_ideal K)
    (delta:[the comNzRingType of (@analytic_germ_ring R X NX hNX a)])
    (sigma:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a):
  I = @AnalyticSetIdeal.value R X NX hNX a (@IdealVarietyGerm.value R X NX hNX a I hI) ->
  ~I delta ->K delta ->
  @IdealVarietyGerm.value R X NX hNX a I hI =
    @SetGerms.join (Topological.clone (real_norm_metric_space hNX) _) a
      (@IdealVarietyGerm.value R X NX hNX a K hK) sigma ->
  sigma<>@set_germ (Topological.clone (real_norm_metric_space hNX) _) a set0.
Proof.
move=>hRecovered hOutside hDelta hVariety hEmpty.
rewrite hEmpty set_germ_union_empty in hVariety.
have hVanishing:=@ideal_in_vanishing_ideal_of_variety R X NX hNX a K hK delta hDelta.
rewrite -hVariety -hRecovered in hVanishing.
exact:hOutside hVanishing.
Qed.
