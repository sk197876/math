(** Federer (1969), 1.6.6, p. 27: the associated space of a nonzero paired
    product is its complex span. In particular it is complex. Source context
    are recorded in ComplexScalarUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SimpleVectors SimpleProducts SimpleWordIndependence
  IndependentProducts ComplexScalarSealed ComplexCharacteristic ScalarRestriction
  ComplexPairedVectors ComplexOrderedBases ComplexSpanComparison ComplexSubspaces
  FiniteSpans FiniteIndependence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Planes.
Variable R : realFieldType.
Local Notation C := (ComplexScalars.C R).
Local Notation hR := (real_two_nonzero R).
Variable V : lmodType C.
Local Notation VR := (restricted_space (ComplexScalars.embed R) V).
Variable p : nat.
Variable v : 'I_p -> V.
Local Notation x := (paired_complex_vector v).
Local Notation b := (e_lambda (ordered_real_basis v) (ord_tuple (p+p))).

(** Source for [paired_vector_block_nonzero]: Federer 1.6.6,
    p. 27, paired representation. Reordering by the fixed sign
    preserves nonvanishing. *)
Lemma paired_vector_block_nonzero : x != 0 -> b != 0.
Proof. by rewrite /paired_complex_vector scaler_eq0 signr_eq0. Qed.

(** Source for [paired_vector_independent]: Federer 1.6.6,
    p. 27, the factors constitute a complex basis of their plane.
    Nonvanishing of the paired product implies complex independence. *)
Lemma paired_vector_independent : x != 0 -> finite_independent v.
Proof.
move=> hx; have hb := paired_vector_block_nonzero hx.
have hw : @exterior_word R VR [seq ordered_real_basis v j | j <- enum 'I_(p+p)] != 0.
  apply/eqP=> hz; apply: (elimT negP hb); apply/eqP; apply: val_inj.
  change (component_val b = component_val (0 : exterior_power VR (p+p))).
  by rewrite e_lambdaE linear0.
apply: real_blocks_independent_complex; exact: nonzero_word_independent hw.
Qed.

(** Source for [independent_paired_vector_nonzero]: Federer
    1.6.6, p. 27, paired product of a complex independent family.
    The ambient space need not be finite-dimensional. *)
Lemma independent_paired_vector_nonzero : finite_independent v -> x != 0.
Proof.
move=> hv; rewrite /paired_complex_vector scaler_eq0 signr_eq0 /=.
exact (@independent_product_nonzero R hR VR (p+p) (ordered_real_basis v)
  (@complex_independent_blocks R V p v hv)).
Qed.

(** Source for [paired_vector_complex_span]: Federer 1.6.6,
    p. 27, complex associated subspace. For a nonzero paired vector,
    its real associated space is exactly the complex span of the v_j. *)
Theorem paired_vector_complex_span : x != 0 -> forall z,
  FedererSimple.T x z <-> in_finite_span v z.
Proof.
move=> hx z; rewrite paired_complex_vector_associated
  (product_associated_space hR (paired_vector_block_nonzero hx)).
exact: complex_real_span.
Qed.

(** Source for [paired_vector_complex]: Federer 1.6.6,
    p. 27, converse in the characterisation of complex simple vectors.
    A nonzero product of real-imaginary pairs has a complex associated plane. *)
Theorem paired_vector_complex : x != 0 -> complex_stable_subspace (FedererSimple.T x).
Proof.
move=> hx z hz; apply/(paired_vector_complex_span hx).
apply: in_finite_span_scale.
exact: (proj1 (paired_vector_complex_span hx z) hz).
Qed.
End Planes.
