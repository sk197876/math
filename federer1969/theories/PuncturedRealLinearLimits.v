(** Federer (1969), 2.9.22, p. 167: the map sending alpha to (alpha o g)'(x)
    is linear. These supporting finite scalar limit laws supply the
    algebraic step, directly from the epsilon definition. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import RealCurveDerivativeUP RealCurveDerivativeLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [punctured_real_limit_add]: supporting linearity
    of scalar limits used to form an element of Y** in Federer
    2.9.22, p. 167. A common radius and two half-epsilon
    estimates prove addition for all nonzero increments. *)
Lemma punctured_real_limit_add (R : realType) (u v : R -> R) a b :
  punctured_real_limit u a -> punctured_real_limit v b ->
  punctured_real_limit (fun h => u h+v h) (a+b).
Proof.
move=> hu hv e he.
have he2 : 0<e/2 by rewrite divr_gt0 // ltr0n.
have [du [hdu hU]] := hu (e/2) he2.
have [dv [hdv hV]] := hv (e/2) he2.
exists (Num.min du dv); split; first by rewrite lt_min hdu hdv.
move=> h /andP [hh hhd].
have hmu : Num.min du dv<=du by rewrite ge_min lexx.
have hmv : Num.min du dv<=dv by rewrite ge_min lexx orbT.
have hhu : 0<`|h|<du by apply/andP; split=> //; exact: lt_le_trans hhd hmu.
have hhv : 0<`|h|<dv by apply/andP; split=> //; exact: lt_le_trans hhd hmv.
have hu' := hU h hhu; have hv' := hV h hhv.
have heq : (u h+v h)-(a+b)=(u h-a)+(v h-b) by ring.
rewrite heq; have ht := ler_normD (u h-a) (v h-b).
by lra.
Qed.

(** Source for [punctured_real_limit_scale]: supporting scalar
    multiplication law for the dual-derivative functional in Federer
    2.9.22, p. 167. The cutoff uses |c|+1, so the zero
    multiplier requires no exceptional convention. *)
Lemma punctured_real_limit_scale (R : realType) (u : R -> R) a c :
  punctured_real_limit u a ->
  punctured_real_limit (fun h => c*u h) (c*a).
Proof.
move=> hu e he.
have hc := normr_ge0 c.
have hC : 0<`|c|+1 by lra.
have he' : 0<e/(`|c|+1) by rewrite divr_gt0.
have [d [hd hB]] := hu _ he'.
exists d; split=> // h hh.
have hb := hB h hh.
have hm : (`|c|+1)*`|u h-a|<e.
  by move: hb; rewrite ltr_pdivlMr // mulrC.
rewrite -mulrBr normrM.
have hle : `|c|*`|u h-a|<=(`|c|+1)*`|u h-a|.
  by rewrite mulrDl mul1r lerDl normr_ge0.
exact: le_lt_trans hle hm.
Qed.
