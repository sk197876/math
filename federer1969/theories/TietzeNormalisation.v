(** General-topology background explicitly invoked by Federer (1969), 2.3.6,
    p. 77: Tietze extension of real functions. The scalar normalisation
    below reduces unbounded Tietze extension to its bounded form. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology
  pseudometric_normed_Zmodule normed_module.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.

(** Source for [tietze_positive_denominator]: supporting positive
    normalisation for the Tietze theorem cited in Federer 2.3.6,
    p. 77; not a separate claim of Federer. *)
Lemma tietze_positive_denominator (R : realType) (x : R) : 0 < 1 + `|x|.
Proof.
have h : 1 <= 1 + `|x| by rewrite lerDl normr_ge0.
exact: lt_le_trans ltr01 h.
Qed.

(** Source for [tietze_reciprocal_normalisation_bound]: supporting
    bounded positive function 1/(1+|f|) for the Tietze citation
    in Federer 2.3.6, p. 77. *)
Lemma tietze_reciprocal_normalisation_bound (R : realType) (x : R) :
  0 < (1 + `|x|)^-1 /\ `|(1 + `|x|)^-1| <= 1.
Proof.
have hp := tietze_positive_denominator x; split; first by rewrite invr_gt0.
rewrite normrV; last by rewrite unitfE; exact: lt0r_neq0 hp.
rewrite (ger0_norm (ltW hp)).
by rewrite (invf_le1 hp) lerDl normr_ge0.
Qed.

(** Source for [tietze_signed_normalisation_bound]: supporting
    bounded function f/(1+|f|) for the Tietze citation in
    Federer 2.3.6, p. 77. *)
Lemma tietze_signed_normalisation_bound (R : realType) (x : R) :
  `|x / (1 + `|x|)| <= 1.
Proof.
have hp := tietze_positive_denominator x.
rewrite normrM normrV; last by rewrite unitfE; exact: lt0r_neq0 hp.
rewrite (ger0_norm (ltW hp)).
rewrite ler_pdivrMr //; by rewrite mul1r lerDr ler01.
Qed.
