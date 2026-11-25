(** Federer (1969), 4.1.5, p. 350: elementary
    scalar laws for the positive-tail cutoff. The
    quotient formula below is used only to prove
    existence of the independently specified cutoff. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_tail_scalar_ratio_laws]: the
    actual scalar witness of h||w||=(||w||-eta)+
    in Federer 4.1.5, p. 350. The zero norm
    and all positive eta are included. *)
Lemma norm_tail_scalar_ratio_laws (R:realType) (t eta:R):
  0<=t ->0<eta ->
  (0<=Num.max (t-eta) 0/t<= 1) /\
  ((Num.max (t-eta) 0/t)*t=Num.max (t-eta) 0) /\
  (t<eta ->Num.max (t-eta) 0/t=0) /\
  (0<=t-Num.max (t-eta) 0<=eta).
Proof.
move=>ht hEta.
have hA:0<=Num.max (t-eta) 0 by rewrite le_max lexx orbT.
have hAT:Num.max (t-eta) 0<=t by rewrite ge_max ht andbT; lra.
case:(eqVneq t 0)=>[hz|hn].
- have hNeg:-eta<=0 by lra.
  rewrite hz sub0r (max_r hNeg) mul0r mulr0 subr0.
  split; first by rewrite lexx ler01.
  split; first reflexivity.
  split; first by [].
  apply/andP; split; first exact:lexx.
  exact:ltW hEta.
- have hPositive:0<t by rewrite lt_neqAle eq_sym hn ht.
  split.
  + apply/andP; split; first exact:divr_ge0 hA ht.
    by rewrite ler_pdivrMr // mul1r.
  + split; first by rewrite divfK.
    split.
    * move=>hSmall.
      have hNeg:t-eta<=0 by lra.
      by rewrite (max_r hNeg) mul0r.
    * apply/andP; split; first by rewrite subr_ge0.
      have hLower:t-eta<=Num.max (t-eta) 0 by rewrite le_max lexx.
      lra.
Qed.
