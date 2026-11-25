(** Federer (1969), 3.4.5, p. 320: the
    original vanishing subset is an actual ideal of the
    analytic germ ring. The proof uses only the sealed
    representative equations and local vanishing laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric AnalyticGermRepresentatives AnalyticGermUP AnalyticGermSealed
  AnalyticGermRingLaws AnalyticGermRing SetGermUP SetGermLaws CommutativeIdealUP
  GermVanishingUP GermVanishingLaws GermVanishingSealed GermVanishingRepresentative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Ideal.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variable a:X.
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation A:=[the comNzRingType of (@analytic_germ_ring R X NX hNX a)].
Local Notation P:=(@analytic_representative_type R X NX hNX a).
Local Notation value:=(@analytic_representative_value R X NX hNX a).
Local Notation germ:=(@analytic_germ R X NX hNX a).
Local Notation sgerm:=(@set_germ T a).
Local Notation ideal:=(@AnalyticSetIdeal.value R X NX hNX a).

(** Source for [analytic_set_ideal_ring_laws]: ideal
    gamma_a(S) is an ideal, 3.4.5, p. 320.
    Every representative and neighbourhood required by its
    definition is discharged by the actual functional laws. *)
Theorem analytic_set_ideal_ring_laws (sigma:set_germ_space (a:T)):
  @is_commutative_ideal A (ideal sigma).
Proof.
have [S <-]:=@set_germ_has_representative T a sigma.
constructor.
- change (ideal (sgerm S) (@analytic_germ_zero R X NX hNX a)).
  apply/(analytic_set_ideal_representative_equation _ S).
  exact:(@vanishes_near_zero T [the comNzRingType of (R:Type)] a S).
- move=>alpha beta hAlpha hBeta.
  have [f hf]:=@analytic_germ_has_representative R X NX hNX a alpha.
  have [g hg]:=@analytic_germ_has_representative R X NX hNX a beta.
  rewrite -hf -hg in hAlpha hBeta *.
  change (ideal (sgerm S) (@AnalyticGerms.add R X NX hNX a (germ f) (germ g))).
  rewrite (@analytic_germ_add_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R X NX hNX a)).
  apply/(analytic_set_ideal_representative_equation _ S).
  exact:(@vanishes_near_add T [the comNzRingType of (R:Type)] a S (value f) (value g)
    ((analytic_set_ideal_representative_equation f S).1 hAlpha)
    ((analytic_set_ideal_representative_equation g S).1 hBeta)).
- move=>alpha hAlpha;have [f hf]:=@analytic_germ_has_representative R X NX hNX a alpha.
  rewrite -hf in hAlpha *.
  change (ideal (sgerm S) (@AnalyticGerms.opp R X NX hNX a (germ f))).
  rewrite (@analytic_germ_negate_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R X NX hNX a)).
  apply/(analytic_set_ideal_representative_equation _ S).
  exact:(@vanishes_near_opp T [the comNzRingType of (R:Type)] a S (value f)
    ((analytic_set_ideal_representative_equation f S).1 hAlpha)).
- move=>alpha beta hBeta.
  have [f hf]:=@analytic_germ_has_representative R X NX hNX a alpha.
  have [g hg]:=@analytic_germ_has_representative R X NX hNX a beta.
  rewrite -hf -hg in hBeta *.
  change (ideal (sgerm S) (@AnalyticGerms.mul R X NX hNX a (germ f) (germ g))).
  rewrite (@analytic_germ_multiply_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R X NX hNX a)).
  apply/(analytic_set_ideal_representative_equation _ S).
  exact:(@vanishes_near_mul T [the comNzRingType of (R:Type)] a S (value f) (value g)
    ((analytic_set_ideal_representative_equation g S).1 hBeta)).
Qed.
End Ideal.
