(** Federer (1969), 3.2.7, p. 246:
    the weight 1+c retains the nonmeasurable set c
    on a finite single branch, while its full periodic
    multiplicity product can lose that information. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialFunctionPreimages CharacteristicFunctionUP MeasurableFunctionUP MeasureUP CountableOrderIntervals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [shifted_characteristic_cutoff_requires_measurable]:
    supporting nonmeasurability test for the first
    example of Federer 3.2.7, p. 246. The
    open superlevel set above three halves is exactly
    B, even after the weight is cut off to E containing B. *)
Lemma shifted_characteristic_cutoff_requires_measurable (R:realType) (X:choiceType)
    (mu:set X->\bar R) (B E:set X) (c chi:X->R):
  B `<=` E -> is_characteristic_function B c -> is_characteristic_function E chi ->
  is_measure_measurable_function mu
    (partial_function_total (fun x=>(((1+c x)*chi x)%:E:extended_real_line R))) ->
  measure_measurable mu B.
Proof.
move=>hBE hc hChi hMeas.
pose F:=partial_function_total (fun x=>(((1+c x)*chi x)%:E:extended_real_line R)).
have he:partial_function_preimage F [set t|((3/2)%R%:E<t)%E]=B.
  apply/seteqP; split=>x.
  - move=>[z [hz hGt]]; change (((1+c x)*chi x)%:E=z) in hz.
    change (is_true (((3/2)%R%:E<z)%E)) in hGt.
    apply:contrapT=>hNot.
    rewrite -hz (characteristic_off_set hc hNot) addr0 in hGt.
    clear hz z.
    case:(pselect (E x))=>hxE.
    + rewrite (characteristic_on_set hChi hxE) mulr1 lte_fin in hGt; lra.
    + rewrite (characteristic_off_set hChi hxE) mulr0 lte_fin in hGt; lra.
  - move=>hx; exists (2:R)%:E; split.
    + change (((1+c x)*chi x)%:E=(2:R)%:E).
      by rewrite (characteristic_on_set hc hx) (characteristic_on_set hChi (hBE x hx)) mulr1.
    + change (is_true (((3/2)%R%:E<(2%R:R)%:E)%E)).
      rewrite lte_fin; lra.
rewrite -he; exact (measurable_function_open_preimage hMeas (order_strict_upper_ray_open _)).
Qed.

(** Source for [shifted_characteristic_positive_bounded]:
    the weight g= 1+c in the first example of
    Federer 3.2.7, p. 246, lies between
    one and two regardless of measurability of c. *)
Lemma shifted_characteristic_positive_bounded (R:realType) (X:Type) (B:set X) (c:X->R):
  is_characteristic_function B c -> forall x,1<= 1+c x /\ 1+c x<= 2.
Proof.
move=>hc x; case:(pselect (B x))=>hx.
- rewrite (characteristic_on_set hc hx); split; lra.
- rewrite (characteristic_off_set hc hx) addr0; split; lra.
Qed.
