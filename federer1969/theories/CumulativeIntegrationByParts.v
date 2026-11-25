(** Federer (1969), 2.6.7, printed p. 121: integration by parts for
    cumulative functions with opposite endpoint conventions. The proof is
    the two Fubini computations printed there, followed by addition of the
    finite constants. The integrands below are zero extensions from the
    indicated half-open intervals, the subset-integral convention of 2.4.10,
    p. 85. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology ring.
From Federer Require Import MeasureUP MeasureIntegralUP SummableRealFunctionUP
  SummableRealArithmetic CharacteristicFunctionUP MeasureCharacteristicIntegral
  RealOrderTriangle RealCumulativeTriangleIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [left_half_open_integrand]: zero extension of
    a real integrand from [a,b), used in the second term
    of Federer 2.6.7, p. 121. *)
Definition left_half_open_integrand (R : realType) (a b : R) (f : R -> R) x :=
  if (a <= x) && (x < b) then f x else 0.

(** Source for [right_half_open_integrand]: zero extension of
    a real integrand from (a,b], used in the first term
    of Federer 2.6.7, p. 121. *)
Definition right_half_open_integrand (R : realType) (a b : R) (f : R -> R) x :=
  if (a < x) && (x <= b) then f x else 0.

(** Source for [left_half_open_characteristic]: the [a,b)
    characteristic function used for the constant terms in
    Federer 2.6.7, p. 121, by 2.4.5, p. 83. *)
Lemma left_half_open_characteristic (R : realType) (a b : R) :
  is_characteristic_function [set x | a <= x /\ x < b]
    (left_half_open_integrand a b (fun _ => 1)).
Proof.
constructor=> x hx; rewrite /left_half_open_integrand.
- by have [hax hxb] := hx; rewrite hax hxb.
- case: ifP=> // /andP [hax hxb]; exfalso; exact: hx (conj hax hxb).
Qed.

(** Source for [right_half_open_characteristic]: the (a,b]
    characteristic function used for the constant terms in
    Federer 2.6.7, p. 121, including a possible atom at b. *)
Lemma right_half_open_characteristic (R : realType) (a b : R) :
  is_characteristic_function [set x | a < x /\ x <= b]
    (right_half_open_integrand a b (fun _ => 1)).
Proof.
constructor=> x hx; rewrite /right_half_open_integrand.
- by have [hax hxb] := hx; rewrite hax hxb.
- case: ifP=> // /andP [hax hxb]; exfalso; exact: hx (conj hax hxb).
Qed.

(** Source for [cumulative_integration_by_parts]: the displayed
    identity in Federer 2.6.7, p. 121. The two subset
    integrals are actually finite. Measurable half-lines suffice
    for the proof; the public Radon specialisation supplies these
    hypotheses. Equality a=b is additionally allowed and yields
    two empty interval integrals. *)
Theorem cumulative_integration_by_parts (R : realType)
    (alpha beta : set R -> \bar R) (ha : is_measure alpha) (hb : is_measure beta)
    (a b : R) (f g : R -> R) :
  (forall t, measure_measurable alpha [set x | x < t]) ->
  (forall t, measure_measurable beta [set x | x <= t]) -> a <= b ->
  (forall r, a <= r -> r <= b -> alpha [set x | x < r]=(f r)%:E) ->
  (forall r, a <= r -> r <= b -> beta [set x | x <= r]=(g r)%:E) ->
  exists I J : R,
    is_measure_integral beta (real_total_integrand (right_half_open_integrand a b f)) I%:E /\
    is_measure_integral alpha (real_total_integrand (left_half_open_integrand a b g)) J%:E /\
    I+J=f b*g b-f a*g a.
Proof.
move=> hAr hBr hab hf hg.
have [s [hsB hsA]] := @cumulative_triangle_fubini R alpha beta ha hb hAr hBr a b hab f g hf hg.
pose cA := left_half_open_integrand a b (fun _ : R => 1).
pose cB := right_half_open_integrand a b (fun _ : R => 1).
have hA := @lower_open_rays_left_interval R alpha ha hAr a b.
have hB := @lower_closed_rays_right_interval R beta hb hBr a b.
have hAv := @lower_open_interval_measure R alpha ha a b (f a) (f b)
  hab (hAr a) (hf a (lexx _) hab) (hf b hab (lexx _)).
have hBv := @lower_closed_interval_measure R beta hb a b (g a) (g b)
  hab (hBr a) (hg a (lexx _) hab) (hg b hab (lexx _)).
have hcA : is_measure_integral alpha (real_total_integrand cA) (f b-f a)%:E.
  rewrite -hAv; exact (@measure_characteristic_integral R R alpha ha _ cA
    (left_half_open_characteristic a b) hA).
have hcB : is_measure_integral beta (real_total_integrand cB) (g b-g a)%:E.
  rewrite -hBv; exact (@measure_characteristic_integral R R beta hb _ cB
    (right_half_open_characteristic a b) hB).
have hi := @real_total_integral_add R R beta hb _ _ s (f a*(g b-g a)) hsB
  (@real_total_integral_scale R R beta hb cB (g b-g a) (f a) hcB).
have hj := @real_total_integral_subtract R R alpha ha _ _ (g b*(f b-f a)) s
  (@real_total_integral_scale R R alpha ha cA (f b-f a) (g b) hcA) hsA.
have heB : (fun y => (if (a < y) && (y <= b) then f y-f a else 0)+f a*cB y)=
    right_half_open_integrand a b f.
  apply: funext=> y; rewrite /cB /right_half_open_integrand; case: ifP=> _; ring.
have heA : (fun x => g b*cA x-(if (a <= x) && (x < b) then g b-g x else 0))=
    left_half_open_integrand a b g.
  apply: funext=> x; rewrite /cA /left_half_open_integrand; case: ifP=> _; ring.
rewrite heB in hi; rewrite heA in hj.
exists (s+f a*(g b-g a)),(g b*(f b-f a)-s); split=> //; split=> //; ring.
Qed.
