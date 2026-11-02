(** Federer (1969), 3.1.1, p. 211: inclusion of the reduced
    closed linear target induces an isometric inclusion of its
    operator space into the original operator space. All carriers
    remain abstract; the witness is chosen only inside an opaque
    existence proof and its evaluation law is exposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom ModuleQuotient SubspaceCarrier RealNormUP NormedSubspace
  NormDifferentialUP NormOperatorNormUP ContinuousOperatorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Inclusion.
Variable R : realType.
Variables X Y Z : lmodType R.
Variable NX : X -> R.
Variable NY : Y -> R.
Variable S : subspace Y.
Variable Z0 : lmodType R.
Variable evaluation : Hom Z (Hom X Y).
Variable ZN : Z -> R.
Hypothesis hZ : is_continuous_operator_space NX NY evaluation ZN.
Variable evaluation0 : Hom Z0 (Hom X (subspace_space S)).
Variable ZN0 : Z0 -> R.
Hypothesis hZ0 : is_continuous_operator_space NX (subspace_norm NY S) evaluation0 ZN0.

(** Source for [continuous_operator_subspace_inclusion_exists]:
    supporting identification of the operator spaces in the
    separable-target reduction, 3.1.1, p. 211. *)
Theorem continuous_operator_subspace_inclusion_exists :
  exists j : Hom Z0 Z, forall z x,
    evaluation (j z) x=subspace_val (evaluation0 z x).
Proof.
pose inc := hom_of_linear (@subspace_inclusion R Y S).
have hex z : exists w, evaluation w=hom_comp inc (evaluation0 z).
  apply: (continuous_operator_surjective hZ).
  have [C [hC hb]] := continuous_operator_bounded hZ0 z.
  exists C; split=> // x; exact: hb x.
pose g z := projT1 (cid (hex z)).
have hg z := projT2 (cid (hex z)).
have hgx z x : evaluation (g z) x=subspace_val (evaluation0 z x).
  by rewrite hg hom_compE.
have hlin : linear g.
  move=> c u v; apply: (continuous_operator_injective hZ); apply: hom_ext=> x.
  rewrite hgx (hom_linear evaluation).
  change (subspace_val (evaluation0 (c *: u+v) x)=
    c *: evaluation (g u) x+evaluation (g v) x).
  rewrite !hgx (hom_linear evaluation0).
  change (subspace_val (c *: evaluation0 u x+evaluation0 v x)=
    c *: subspace_val (evaluation0 u x)+subspace_val (evaluation0 v x)).
  exact: (linearP (@subspace_inclusion R Y S)).
exists (@HomMap R Z0 Z g (introT (asboolP _) hlin)); exact hgx.
Qed.

Variable j : Hom Z0 Z.
Hypothesis hj : forall z x, evaluation (j z) x=subspace_val (evaluation0 z x).

(** Source for [continuous_operator_subspace_inclusion_isometry]:
    the inclusion preserves the least operator norm, supporting
    the Borel target reduction in 3.1.1, p. 211. *)
Lemma continuous_operator_subspace_inclusion_isometry z : ZN (j z)=ZN0 z.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (norm_operator_least (continuous_operator_norm_laws hZ (j z))
    (norm_operator_nonnegative (continuous_operator_norm_laws hZ0 z)))=> x.
  rewrite hj; exact: norm_operator_bound (continuous_operator_norm_laws hZ0 z) x.
- apply: (norm_operator_least (continuous_operator_norm_laws hZ0 z)
    (norm_operator_nonnegative (continuous_operator_norm_laws hZ (j z))))=> x.
  have hb := norm_operator_bound (continuous_operator_norm_laws hZ (j z)) x.
  by rewrite hj in hb.
Qed.

(** Source for [continuous_operator_subspace_inclusion_injective]:
    injectivity of the operator inclusion used before applying
    the Borel projection theorem in 3.1.1, p. 211. *)
Lemma continuous_operator_subspace_inclusion_injective : injective j.
Proof.
move=> u v huv; apply: (continuous_operator_injective hZ0); apply: hom_ext=> x.
apply: subspace_val_injective; by rewrite -!hj huv.
Qed.

(** Source for [continuous_operator_subspace_inclusion_represents]:
    every bounded operator with image in the reduced target is
    represented by its operator space, supporting 3.1.1, p. 211. *)
Lemma continuous_operator_subspace_inclusion_represents (L : Hom X Y) :
  norm_bounded_linear NX NY L -> (forall x, S (L x)) ->
  exists z, evaluation (j z)=L.
Proof.
move=> [C [hC hb]] hLS.
pose L0 := hom_comp (hom_of_linear (@subspace_retraction R Y S)) L.
have hL0 x : subspace_val (L0 x)=L x.
  exact: (subspace_retraction_on (hLS x)).
have hb0 : norm_bounded_linear NX (subspace_norm NY S) L0.
  exists C; split=> // x; rewrite /subspace_norm hL0; exact: hb x.
have [z hz] := continuous_operator_surjective hZ0 hb0.
exists z; apply: hom_ext=> x; by rewrite hj hz hL0.
Qed.
End Inclusion.
