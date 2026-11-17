(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(10), p. 331:
    assemble the original variety-germ equation
    from the proved positive-power assertion and
    the original Boolean germ laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed RealNormUP NormMetric HolomorphicGermUP HolomorphicGermRing
  SetGermUP SetGermSealed SetGermDifferenceOrder CommutativeIdealUP HolomorphicZeroGermSealed
  HolomorphicIdealVarietyGermSealed HolomorphicIdealVarietyAdjoinEquation HolomorphicSaturationVariety.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [equation_saturation_variety_recovery]:
    var(I_g)=var(J) union gamma_0(Z), with
    Z the zero system of F
    outside delta=0, 3.4.8(10), p. 331.
    Here the equation-system part is expressed
    by the original opaque germ operations;
    actual representatives are connected separately. *)
Theorem equation_saturation_variety_recovery (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X)
    (I F J:set [the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)])
    (hI:is_finitely_generated_commutative_ideal I)
    (hF:is_finitely_generated_commutative_ideal F)
    (hJ:is_finitely_generated_commutative_ideal J) delta:
  F `<=` I ->
  (forall alpha,I alpha ->exists u:nat,(0<u)%N /\F (delta^+u*alpha)) ->
  is_generated_commutative_ideal (I `|` [set alpha|alpha = delta]) J ->
  @HolomorphicIdealVarietyGerm.value R X NX hNX a I hI =
    @SetGerms.join (Topological.clone (real_norm_metric_space hNX) _) a
      (@HolomorphicIdealVarietyGerm.value R X NX hNX a J hJ)
      (@SetGerms.meet (Topological.clone (real_norm_metric_space hNX) _) a
        (@HolomorphicIdealVarietyGerm.value R X NX hNX a F hF)
        (@SetGerms.neg (Topological.clone (real_norm_metric_space hNX) _) a
          (@HolomorphicZeroGerm.value R X NX hNX a delta))).
Proof.
move=>hFI hPower hGenerated.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
pose varI:=@HolomorphicIdealVarietyGerm.value R X NX hNX a I hI.
pose zero:=@HolomorphicZeroGerm.value R X NX hNX a delta.
transitivity (@SetGerms.join T a (@SetGerms.meet T a varI zero)
    (@SetGerms.meet T a varI (@SetGerms.neg T a zero))).
- exact:set_germ_split_equation.
- rewrite -(@ideal_variety_adjoin_equation R X NX hNX a I J hI hJ delta hGenerated)
    (@holomorphic_saturation_variety_off_equation R X NX hNX a I F hI hF delta hFI hPower).
  by [].
Qed.
