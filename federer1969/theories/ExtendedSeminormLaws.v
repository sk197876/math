(** Federer (1969), 2.4.12, p. 86, opening paragraph: the finite-value locus
    of a seminorm is a vector subspace. Source context and the
    partial-function-space correction: ExtendedSeminormUP.v. These
    consequences use only the abstract extended-seminorm laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import ExtendedSeminormUP ModuleQuotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Section Laws.
Variable R : realType.
Variable V : lmodType R.
Variable N : V -> \bar R.
Hypothesis hN : is_extended_seminorm N.

(** Source for [extended_seminorm_zero]: supporting consequence
    of absolute homogeneity in Federer 2.4.12, p. 86,
    including the explicitly stipulated zero-times-infinity convention. *)
Lemma extended_seminorm_zero : N 0%R = 0.
Proof.
have h := extended_seminorm_scale hN 0%R (0 : V).
by move: h; rewrite scale0r normr0 mul0e.
Qed.

(** Source for [extended_seminorm_negate]: supporting symmetry
    consequence of the seminorm definition in Federer 2.4.12,
    p. 86. *)
Lemma extended_seminorm_negate x : N (-x)%R=N x.
Proof. by rewrite -scaleN1r (extended_seminorm_scale hN) normrN normr1 mul1e. Qed.

(** Source for [extended_seminorm_finite_locus]: the vector
    subspace displayed immediately after the seminorm definition
    in Federer 2.4.12, p. 86. This predicate defines
    its elements independently of any subspace implementation. *)
Definition extended_seminorm_finite_locus x := N x < +oo.

(** Source for [extended_seminorm_finite_zero]: zero belongs
    to the subspace in Federer 2.4.12, p. 86. *)
Lemma extended_seminorm_finite_zero : extended_seminorm_finite_locus 0%R.
Proof. by rewrite /extended_seminorm_finite_locus extended_seminorm_zero ltry. Qed.

(** Source for [extended_seminorm_finite_add]: addition closure
    of the subspace displayed in Federer 2.4.12, p. 86. *)
Lemma extended_seminorm_finite_add x y :
  extended_seminorm_finite_locus x -> extended_seminorm_finite_locus y ->
  extended_seminorm_finite_locus (x+y)%R.
Proof.
move=> hx hy; apply: le_lt_trans (extended_seminorm_triangle hN x y) _.
exact: lte_add_pinfty hx hy.
Qed.

(** Source for [extended_seminorm_finite_scale]: scalar closure
    of the subspace displayed in Federer 2.4.12, p. 86. *)
Lemma extended_seminorm_finite_scale (c : R) x :
  extended_seminorm_finite_locus x -> extended_seminorm_finite_locus (c *: x)%R.
Proof.
move=> hx; have hfin : N x \is a fin_num by rewrite (ge0_fin_numE (extended_seminorm_nonnegative hN x)).
rewrite /extended_seminorm_finite_locus (extended_seminorm_scale hN) -(fineK hfin) -EFinM.
exact: ltry.
Qed.
(** Source for [extended_seminorm_finite_subspace]: the
    explicit subspace assertion in Federer 2.4.12, p. 86.
    The witness proves existence of a subspace with exactly
    the prescribed finite-value membership predicate. *)
Theorem extended_seminorm_finite_subspace : exists S : subspace V,
  forall x, S x <-> extended_seminorm_finite_locus x.
Proof.
exists (@Subspace R V extended_seminorm_finite_locus
  extended_seminorm_finite_zero extended_seminorm_finite_add extended_seminorm_finite_scale).
by move=> x; split.
Qed.
End Laws.
