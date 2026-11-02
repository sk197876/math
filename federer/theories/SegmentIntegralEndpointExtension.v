(** Federer (1969), 2.9.20, p. 166, final proof sentence: use continuity and
    2.4.11 to let the interior interval endpoints approach the
    closed-segment endpoints. The abstract supporting lemma below uses
    existence and small- interval laws for the integral, without
    constructing an extension of the curve outside its segment. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP
  MeasureSubsetIntegral LebesgueScalarMeasure SegmentContinuityControl FiniteIntervalIntegralSplitting.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [interior_segment_endpoint_approximation]: supporting
    simultaneous endpoint approximation for Federer 2.9.20, p. 166, last
    proof sentence Choose two ordered interior points close to the two
    endpoints and with both omitted interval lengths below a common cutoff. *)
Lemma interior_segment_endpoint_approximation (R : realType) (a x da dx di : R) :
  a<x -> 0<da -> 0<dx -> 0<di -> exists u v : R,
    a<u /\ u<v /\ v<x /\ u-a<da /\ x-v<dx /\ u-a<=di /\ x-v<=di.
Proof.
move=> hax hda hdx hdi.
pose m := Num.min da (Num.min dx (Num.min di ((x-a)/4))).
have hg : 0<(x-a)/4 by rewrite divr_gt0 ?subr_gt0 // ltr0n.
have hm : 0<m by rewrite /m !lt_min hda hdx hdi hg.
have hmda : m<=da by rewrite /m ge_min lexx.
have hmt : m<=Num.min dx (Num.min di ((x-a)/4)) by rewrite /m ge_min lexx orbT.
have hmdx : m<=dx.
  apply: le_trans hmt _; by rewrite ge_min lexx.
have hmtt : m<=Num.min di ((x-a)/4).
  apply: le_trans hmt _; by rewrite ge_min lexx orbT.
have hmdi : m<=di.
  apply: le_trans hmtt _; by rewrite ge_min lexx.
have hmg : m<=(x-a)/4.
  apply: le_trans hmtt _; by rewrite ge_min lexx orbT.
exists (a+m/2),(x-m/2); repeat split; lra.
Qed.

(** Source for [segment_integral_identity_extend_endpoints]: direct
    endpoint-limit argument for the last sentence of Federer 2.9.20, p. 166
    Assume the integral identity on strictly interior intervals, existence
    of finite subinterval integrals, and the small-interval consequence of
    2.4.11. Relative continuity controls both omitted increments; finite
    additivity controls the two omitted integrals. A common cutoff and the
    triangle inequality extend the identity to [a,x]. The case x=a is proved
    separately from the same small-integral law. *)
Theorem segment_integral_identity_extend_endpoints (R : realType) (g : R -> R)
    (f : partial_function (real_line_metric R) (extended_real_line R)) (a b : R) :
  a<b ->
  {within (`[a,b] : set (real_line_metric R)),
    continuous (g : real_line_metric R -> real_line_metric R)} ->
  (forall u v : R, a<=u -> u<=v -> v<=b -> exists I : R,
    is_measure_subset_integral (@lebesgue_scalar_measure R) `[u,v] f I%:E) ->
  (forall e : R, 0<e -> exists d : R, 0<d /\ forall u v I : R,
    a<=u -> u<=v -> v<=b -> v-u<=d ->
    is_measure_subset_integral (@lebesgue_scalar_measure R) `[u,v] f I%:E -> `|I|<e) ->
  (forall u v : R, a<u -> u<v -> v<b ->
    is_measure_subset_integral (@lebesgue_scalar_measure R) `[u,v] f (g v-g u)%:E) ->
  forall x : R, a<=x -> x<=b ->
    is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,x] f (g x-g a)%:E.
Proof.
move=> hab hc hExists hSmall hInterior x hax hxb.
case: (eqVneq x a)=> [hxa|hxa].
- rewrite hxa subrr.
  have [I hI] := hExists a a (lexx a) (lexx a) (ltW hab).
  have hIz : I=0.
    have hnorm : `|I|<=0.
      apply/ler_addgt0Pr=> e he; rewrite add0r.
      have [d [hd hcut]] := hSmall e he.
      have hwidth : a-a<=d by rewrite subrr; exact: ltW hd.
      exact: ltW (hcut a a I (lexx a) (lexx a) (ltW hab) hwidth hI).
    have hzero : `|I|=0 by apply/le_anti/andP; split=> //; exact: normr_ge0.
    by move/eqP: hzero; rewrite normr_eq0=> /eqP.
  by rewrite hIz in hI.
- have hax' : a<x by rewrite lt_neqAle eq_sym hxa hax.
  have [I hI] := hExists a x (lexx a) hax hxb.
  have hEq : I=g x-g a.
    apply: contrapT=> hne.
    pose E := `|I-(g x-g a)|/8.
    have hN : 0<`|I-(g x-g a)|.
      rewrite normr_gt0 subr_eq0; exact/eqP.
    have hE : 0<E by rewrite /E divr_gt0 // ltr0n.
    have [di [hdi hcut]] := hSmall E hE.
    have [da [hda hca]] := @segment_continuity_epsilon_control R g a b a E
      hc (lexx a) (ltW hab) hE.
    have [dx [hdx hcx]] := @segment_continuity_epsilon_control R g a b x E hc hax hxb hE.
    have [u [v [hau [huv [hvx [hua [hxv [hui hvi]]]]]]]] :=
      interior_segment_endpoint_approximation hax' hda hdx hdi.
    have haux : a<=u := ltW hau.
    have huvx : u<=v := ltW huv.
    have hvxx : v<=x := ltW hvx.
    have hub : u<=b := le_trans huvx (le_trans hvxx hxb).
    have hvb : v<=b := le_trans hvxx hxb.
    have hav : a<=v := le_trans haux huvx.
    have hInt := hInterior u v hau huv (lt_le_trans hvx hxb).
    have [A hA] := hExists a u (lexx a) haux hub.
    have [B hB] := hExists a v (lexx a) hav hvb.
    have [C hC] := hExists v x hav hvxx hxb.
    have hsplit1 := @finite_lebesgue_interval_integral_split R f a u v B A (g v-g u)
      haux huvx hB hA hInt.
    have hsplit2 := @finite_lebesgue_interval_integral_split R f a v x I B C
      hav hvxx hI hB hC.
    have hASmall := hcut a u A (lexx a) haux hub hui hA.
    have hCSmall := hcut v x C hav hvxx hxb hvi hC.
    have huNorm : `|u-a|<da by rewrite ger0_norm ?subr_ge0 //.
    have hvNorm : `|v-x|<dx by rewrite distrC ger0_norm ?subr_ge0 //.
    have hgu := hca u haux hub huNorm.
    have hgv := hcx v hav hvb hvNorm.
    have hdecomp : I-(g x-g a)=A+C+(g v-g x)-(g u-g a).
      rewrite hsplit2 hsplit1; ring.
    have hn1 := ler_normD A C.
    have hn2 := ler_normD (A+C) (g v-g x).
    have hn3 := ler_normB (A+C+(g v-g x)) (g u-g a).
    rewrite -hdecomp in hn3.
    rewrite /E in hASmall hCSmall hgu hgv.
    exfalso; lra.
  by rewrite hEq in hI.
Qed.
