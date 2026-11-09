(** Federer (1969), 3.4.6(2), p. 322: an
    actual monic transverse expression verifies the original
    preparation laws with multiplier one. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP NormAnalyticUP AnalyticGermNeighbourhood AnalyticGermRepresentatives
  AnalyticGermUP AnalyticGermRing WeierstrassPreparationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weierstrass_monic_preparation_candidate]:
    a literal original monic polynomial with actual analytic
    transverse coefficients zero at the origin satisfies
    every preparation law, testing 3.4.6(2), p. 322.
    This is verification of a concrete candidate, rather
    than an assumption of existence or uniqueness. *)
Theorem weierstrass_monic_preparation_candidate (R:realType) (X K:lmodType R)
    (NX:X->R) (NK:K->R) (hNX:is_real_norm NX) (hNK:is_real_norm NK)
    (xi:Hom X R^o) (projection:Hom X K) k
    (phi:analytic_representative_type hNX (0:X))
    (c:'I_k->analytic_representative_type hNK (0:K)):
  (forall i,analytic_representative_value (c i) 0=0) ->
  (forall x,analytic_representative_value phi x=(xi x)^+k+
    \sum_(i<k) (xi x)^+i*analytic_representative_value (c i) (projection x)) ->
  @is_weierstrass_preparation R X K NX NK hNX hNK xi projection k
    (analytic_germ phi) 1 (analytic_germ phi) (fun i=>analytic_germ (c i)).
Proof.
move=>hZero hValues;constructor.
- exact:mul1r.
- exists (@analytic_constant_representative R X NX hNX 0 1);split;first reflexivity.
  change ((1:R)<>0);apply/eqP;exact:oner_neq0 R.
- exists phi;split;first reflexivity.
  exists c;split;first by move=>i.
  split;first exact:hZero.
  have [U [ha [_ [_ hf]]]]:=@analytic_germ_open_representative R X R^o NX (fun r=>`|r|)
    hNX (@scalar_absolute_value_norm R) setT (analytic_representative_value phi) 0 (analytic_representative_analytic phi).
  exists U;split;first exact:ha.
  split;first exact:hf.
  move=>x _;exact:hValues x.
Qed.
