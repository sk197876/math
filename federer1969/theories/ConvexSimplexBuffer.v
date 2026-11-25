(** Supporting convex geometry for Federer (1969), 2.10.5(2), p. 173, and
    the forward reference 3.2.36, p. 272. A simplex contained in a convex
    set contains a fixed coordinate box about its barycentre. This is the
    finite convex-combination background of 1.8.1, p. 38, not a separate
    printed measure assertion. Neither item states this explicit
    coordinate-buffer bound. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets.
From mathcomp Require Import lra.
From Federer Require Import InnerConvex ConvexFiniteCombinations ConvexTranslatedCombinations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [simplex_barycentre_coordinate_bounds]:
    supporting positive barycentric coordinates
    for the convex-set arguments behind Federer
    2.10.5(2), p. 173. The explicit box radius
    is 1/(m+1)^2, with the empty-coordinate
    case included. *)
Lemma simplex_barycentre_coordinate_bounds (R : realFieldType) m (z : 'I_m -> R) :
  (forall i, `|z i|<=((m.+1)%:R:R)^-1^+2) ->
  (forall i, 0<=((m.+1)%:R:R)^-1+z i) /\
    \sum_i (((m.+1)%:R:R)^-1+z i)<=1.
Proof.
move=> hz.
pose c : R := ((m.+1)%:R)^-1.
have hc : 0<c by rewrite /c invr_gt0 ltr0n.
have hc1 : c<=1 by rewrite /c invf_le1 ?ler1n // ltr0n.
have hcN : (m.+1)%:R!=0 :> R by rewrite pnatr_eq0.
have hsum : m%:R*c+c = 1.
  have hmul : ((m.+1)%:R:R)*c = 1 by rewrite /c mulfV.
  by rewrite -addn1 natrD mulrDl mul1r in hmul.
have hcsq : c^+2<=c.
  have h := ler_wpM2l (ltW hc) hc1; by rewrite mulr1 -expr2 in h.
have hmsq : m%:R*c^+2<=c.
  have hmc : m%:R*c<=1 by lra.
  have h := ler_wpM2r (ltW hc) hmc; by rewrite mul1r -mulrA -expr2 in h.
split.
- move=> i; have hh := hz i; change (is_true (`|z i|<=c^+2)) in hh.
  change (is_true (0<=c+z i)).
  move: hh; rewrite ler_norml=> /andP[hl hu]; lra.
- change (is_true (\sum_i (c+z i)<=1)).
  have hsumz : \sum_i z i<=m%:R*c^+2.
    have hconst : (\sum_(i : 'I_m) c^+2)=m%:R*c^+2.
      by rewrite sumr_const card_ord mulr_natl.
    rewrite -hconst.
    apply: ler_sum=> i _; exact: le_trans (ler_norm _) (hz i).
  have hmc : c*+m=m%:R*c by rewrite mulr_natl.
  rewrite big_split sumr_const card_ord hmc.
  apply: le_trans (lerD (lexx (m%:R*c)) hsumz) _.
  apply: le_trans (lerD (lexx (m%:R*c)) hmsq) _.
  by rewrite hsum.
Qed.

(** Source for [convex_simplex_coordinate_buffer]:
    supporting simplex neighbourhood for Federer
    2.10.5(2), p. 173, and 3.2.36, p. 272.
    Small changes of the barycentric coordinates
    remain in the convex set. Independence is
    unnecessary for this combination law. *)
Theorem convex_simplex_coordinate_buffer (R : realFieldType) (V : lmodType R)
    (K : set V) (a : V) m (v : 'I_m -> V) (z : 'I_m -> R) :
  is_inner_convex K -> K a -> (forall i, K (a+v i)) ->
  (forall i, `|z i|<=((m.+1)%:R:R)^-1^+2) ->
  K (a+\sum_i (((m.+1)%:R:R)^-1+z i)*:v i).
Proof.
move=> hK ha hv hz.
pose D := [set x | K (x+a)].
have hD : is_inner_convex D := @convex_translate_to_origin R V K a hK.
have h0 : D 0 by rewrite /D /= add0r.
have hvD i : D (v i) by rewrite /D /= addrC.
have [hpos hsum] := simplex_barycentre_coordinate_bounds hz.
have hh := @convex_subconvex_sum R V D hD h0 m v
  (fun i => ((m.+1)%:R:R)^-1+z i) hvD hpos hsum.
change (K ((\sum_i (((m.+1)%:R:R)^-1+z i)*:v i)+a)) in hh.
by rewrite addrC.
Qed.
