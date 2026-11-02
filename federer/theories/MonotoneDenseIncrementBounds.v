(** Federer (1969), 2.9.19, p. 164: extend increment estimates from
    continuity-point endpoints to all endpoints by monotonicity. Here a
    dense set D records the permitted endpoints, and the base point belongs
    to D. The latter is discharged almost everywhere using the already
    proved countable-discontinuity result. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology lra ring.
From Federer Require Import RealMetricBackground DenseRealOrderPoints.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Bounds.
Variable R : realType.
Variable D : set (real_line_metric R).
Variable g : R -> R.
Variable x : R.
Hypothesis hD : dense D.
Hypothesis hxD : D x.
Hypothesis hmono : forall s t : R, s<=t -> g s<=g t.

(** Source for [monotone_dense_increment_lower_bound]: supporting lower
    increment estimate in Federer 2.9.19, p. 164 Inner endpoint
    perturbations preserve containment of x and approximate the interval
    length. Negative lower coefficients are handled directly by
    monotonicity. No continuity at the arbitrary endpoints is assumed. *)
Lemma monotone_dense_increment_lower_bound (L d a b : R) :
  (forall u v, D u -> D v -> u<=x<=v -> 0<v-u<d -> L*(v-u)<=g v-g u) ->
  a<=x<=b -> 0<b-a<d -> L*(b-a)<=g b-g a.
Proof.
move=> hB /andP [hax hxb] /andP [hw hwd].
have hab : a<=b := le_trans hax hxb.
have hgb : 0<=g b-g a by rewrite subr_ge0; exact: hmono.
case: (leP L 0)=> [hL0|hL].
- have hprod := ler_wpM2r (ltW hw) hL0.
  rewrite mul0r in hprod; exact: le_trans hprod hgb.
- apply/ler_addgt0Pr=> e he.
  pose eta := Num.min ((b-a)/4) (e/(4*L)).
  have hden : 0<4*L by rewrite mulr_gt0 // ltr0n.
  have heta : 0<eta by rewrite /eta lt_min !divr_gt0 // ltr0n.
  have hew : eta<=(b-a)/4 by rewrite /eta ge_min lexx.
  have heE : eta<=e/(4*L) by rewrite /eta ge_min lexx orbT.
  have [u [huD [/andP [hau hux] [hua _]]]] :=
    dense_real_inner_left_endpoint hD hxD hax heta.
  have [v [hvD [/andP [hxv hvb] [hbv _]]]] :=
    dense_real_inner_right_endpoint hD hxD hxb heta.
  have huv : 0<v-u by lra.
  have hwidth : v-u<d := le_lt_trans (lerB hvb hau) hwd.
  have huxv : u<=x<=v by apply/andP; split.
  have huvD : 0<v-u<d by apply/andP; split.
  have hinc := hB u v huD hvD huxv huvD.
  have hmon : g v-g u<=g b-g a := lerB (@hmono v b hvb) (@hmono a u hau).
  have hlow := le_trans hinc hmon.
  have hscale := ler_wpM2l (ltW hL) heE.
  have heq : L*(e/(4*L))=e/4 by field; rewrite (gt_eqF hL).
  rewrite heq in hscale.
  have hgap : (b-a)-(v-u)<eta+eta by lra.
  have hmul : L*((b-a)-(v-u))<L*(eta+eta) by rewrite (ltr_pM2l hL).
  rewrite (mulrBr L (b-a) (v-u)) (mulrDr L eta eta) in hmul.
  have hsmall : L*eta+L*eta<e by lra.
  have herror := lt_trans hmul hsmall.
  apply: ltW; lra.
Qed.

(** Source for [monotone_dense_increment_upper_bound]: supporting upper
    increment estimate in Federer 2.9.19, p. 164 Outer endpoint
    perturbations enlarge the increment and can be chosen to keep the
    interval length strictly below d. The positive upper coefficient is
    explicit; in the application it is the nonnegative derivate plus
    epsilon. *)
Lemma monotone_dense_increment_upper_bound (U d a b : R) : 0<U ->
  (forall u v, D u -> D v -> u<=x<=v -> 0<v-u<d -> g v-g u<=U*(v-u)) ->
  a<=x<=b -> 0<b-a<d -> g b-g a<=U*(b-a).
Proof.
move=> hU hB /andP [hax hxb] /andP [hw hwd].
apply/ler_addgt0Pr=> e he.
pose eta := Num.min ((d-(b-a))/4) (e/(4*U)).
have hden : 0<4*U by rewrite mulr_gt0 // ltr0n.
have heta : 0<eta by rewrite /eta lt_min !divr_gt0 // ?subr_gt0 // ltr0n.
have hew : eta<=(d-(b-a))/4 by rewrite /eta ge_min lexx.
have heE : eta<=e/(4*U) by rewrite /eta ge_min lexx orbT.
have hleft : a-eta<a by lra.
have hright : b<b+eta by lra.
have [u [/andP [hua hau] huD]] := dense_real_open_interval_point hD hleft.
have [v [/andP [hbv hvb] hvD]] := dense_real_open_interval_point hD hright.
have huv : 0<v-u by lra.
have hwidth : v-u<d by lra.
have huxv : u<=x<=v by apply/andP; split; lra.
have huvD : 0<v-u<d by apply/andP; split.
have hinc := hB u v huD hvD huxv huvD.
have hmon : g b-g a<=g v-g u := lerB (@hmono b v (ltW hbv)) (@hmono u a (ltW hau)).
have hupp := le_trans hmon hinc.
have hscale := ler_wpM2l (ltW hU) heE.
have heq : U*(e/(4*U))=e/4 by field; rewrite (gt_eqF hU).
rewrite heq in hscale.
have hgap : (v-u)-(b-a)<eta+eta by lra.
have hmul : U*((v-u)-(b-a))<U*(eta+eta) by rewrite (ltr_pM2l hU).
rewrite (mulrBr U (v-u) (b-a)) (mulrDr U eta eta) in hmul.
have hsmall : U*eta+U*eta<e by lra.
have herror := lt_trans hmul hsmall.
apply: ltW; lra.
Qed.
End Bounds.
