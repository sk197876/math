(** Federer (1969), 1.6.6, p. 27: a real subspace is complex precisely when
    it is invariant under multiplication by i. The subspace predicate is
    retained; complex scalar closure and the comparison of its two carriers
    are proved. Source context are recorded in ComplexScalarUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ModuleQuotient SubspaceCarrier ScalarRestriction
  ComplexScalarUP ComplexScalarSealed ComplexScalarLaws FiniteIndependence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory ComplexScalarTheory.
Local Open Scope ring_scope.
Section Subspaces.
Variable R : realFieldType.
Local Notation C := (ComplexScalars.C R).
Local Notation embed := (ComplexScalars.embed R).
Local Notation ii := (ComplexScalars.ii R).
Variable V : lmodType C.
Local Notation VR := (restricted_space embed V).
Variable S : subspace VR.

(** Source for [complex_stable_subspace]: Federer 1.6.6,
    p. 27, complex associated subspace. Abstract invariance under i. *)
Definition complex_stable_subspace := forall v, S v -> S (ii *: v).

(** Source for [complex_stable_scale]: Federer 1.6.6,
    p. 27, complex subspace condition. Real scalar closure and
    invariance under i imply closure under every complex scalar. *)
Lemma complex_stable_scale : complex_stable_subspace -> forall (z : C) (v : V), S v -> S (z *: v).
Proof.
move=> hs z v hv.
rewrite (complex_decomposition (ComplexScalars.laws R) z) scalerDl mulrC -scalerA.
apply: subspace_add.
- exact: (subspace_scale (@ComplexScalars.re R z) hv).
- exact: (subspace_scale (@ComplexScalars.im R z) (hs v hv)).
Qed.

(** Source for [complex_stable_iff]: Federer 1.6.6, p. 27,
    complex subspace condition. Invariance under i is equivalent to
    invariance under all complex scalars. *)
Lemma complex_stable_iff : complex_stable_subspace <-> forall (z : C) (v : V), S v -> S (z *: v).
Proof. split; [exact: complex_stable_scale | by move=> h; exact: h]. Qed.

Variable hs : complex_stable_subspace.
(** Source for [stable_complex_subspace]: Federer 1.6.6,
    p. 27, complex associated subspace. The same predicate equipped
    with the proved complex vector-space laws. *)
Definition stable_complex_subspace : subspace V :=
  @Subspace C V S (subspace_zero S) (@subspace_add R VR S) (complex_stable_scale hs).
Local Notation SC := (GRing.Lmodule.clone C (subspace_space stable_complex_subspace) _).
Local Notation SR := (GRing.Lmodule.clone R (subspace_space S) _).
Local Notation SCR := (restricted_space embed SC).

(** Source for [stable_subspace_real]: Federer 1.6.6, p. 27,
    real and complex dimensions of a complex plane. Supporting
    identification of the complex carrier with its original real carrier. *)
Definition stable_subspace_real (v : SCR) : SR :=
  @SubspaceVector R VR S (subspace_val v) (subspace_proof v).

(** Source for [stable_subspace_complex]: Federer 1.6.6,
    p. 27, real and complex descriptions of a plane. Inverse carrier
    identification, preserving the underlying vector. *)
Definition stable_subspace_complex (v : SR) : SCR :=
  @SubspaceVector C V stable_complex_subspace (subspace_val v) (subspace_proof v).

(** Source for [stable_subspace_real_linear]: Federer 1.6.6,
    p. 27, real and complex plane. The carrier comparison is real linear. *)
Lemma stable_subspace_real_linear : linear stable_subspace_real.
Proof. by move=> c x y; apply: val_inj. Qed.
HB.instance Definition _ := GRing.isLinear.Build R SCR SR *:%R
  stable_subspace_real stable_subspace_real_linear.

(** Source for [stable_subspace_complex_linear]: Federer
    1.6.6, p. 27, real and complex plane. The inverse comparison
    is real linear. *)
Lemma stable_subspace_complex_linear : linear stable_subspace_complex.
Proof. by move=> c x y; apply: val_inj. Qed.
HB.instance Definition _ := GRing.isLinear.Build R SR SCR *:%R
  stable_subspace_complex stable_subspace_complex_linear.

(** Source for [stable_subspace_realK]: Federer 1.6.6,
    p. 27, real and complex plane. Cancellation of the carrier maps. *)
Lemma stable_subspace_realK : cancel stable_subspace_real stable_subspace_complex.
Proof. by move=> v; apply: val_inj. Qed.

(** Source for [stable_subspace_complexK]: Federer 1.6.6,
    p. 27, real and complex plane. Reverse cancellation of the maps. *)
Lemma stable_subspace_complexK : cancel stable_subspace_complex stable_subspace_real.
Proof. by move=> v; apply: val_inj. Qed.
End Subspaces.

(** Source for [complex_independent_real]: Federer 1.6.6,
    p. 27, even dimension of a complex plane. Supporting bound:
    a complex independent family remains real independent. *)
Lemma complex_independent_real (R : realFieldType) (V : lmodType (ComplexScalars.C R))
  (I : finType) (e : I -> V) : finite_independent e ->
  @finite_independent R I (restricted_space (ComplexScalars.embed R) V) e.
Proof.
move=> he c hc j.
have hz : \sum_i (ComplexScalars.embed R (c i)) *: e i = 0 := hc.
have h := he (fun i => ComplexScalars.embed R (c i)) hz j.
have hr := congr1 (@ComplexScalars.re R) h.
by rewrite re_embed re_zero in hr.
Qed.
