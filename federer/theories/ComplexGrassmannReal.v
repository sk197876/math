(** Federer (1969), 3.4.12, p. 339:
    an original complex m-plane is a real 2m-plane.
    Reuse the paired real basis of 1.6.6, p. 26,
    preserving the exact original subspace predicate. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import ModuleQuotient SubspaceCarrier ScalarRestriction
  ComplexScalarSealed ComplexOrderedBases GrassmannSubspaces LinearBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Subspace.
Variable R:realFieldType.
Variable X:lmodType (ComplexScalars.C R).
Variable S:subspace X.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).

(** Source for [restricted_complex_subspace]: the original
    complex plane Z considered as a real plane in
    3.4.12, p. 339. Its membership predicate
    is unchanged; only scalar closure is restricted. *)
Definition restricted_complex_subspace:subspace XR:=
  @Subspace R XR S (subspace_zero S) (@subspace_add _ X S)
    (fun a x hx=>@subspace_scale _ X S (ComplexScalars.embed R a) x hx).
Local Notation SC:=(GRing.Lmodule.clone (ComplexScalars.C R) (subspace_space S) _).
Local Notation SR:=(GRing.Lmodule.clone R (subspace_space restricted_complex_subspace) _).
Local Notation SCR:=(restricted_space (ComplexScalars.embed R) SC).

(** Source for [restricted_subspace_forward]: identify the
    original complex carrier's realification with its real
    subspace carrier, supporting 3.4.12, p. 339. *)
Definition restricted_subspace_forward (x:SCR):SR:=
  @SubspaceVector R XR restricted_complex_subspace (subspace_val x) (subspace_proof x).

(** Source for [restricted_subspace_backward]: the inverse
    carrier identification for the original plane, supporting
    3.4.12, p. 339. *)
Definition restricted_subspace_backward (x:SR):SCR:=
  @SubspaceVector (ComplexScalars.C R) X S (subspace_val x) (subspace_proof x).

(** Source for [restricted_subspace_forward_linear]: the original
    carrier identification is real linear, as required by
    the real dimension comparison in 3.4.12, p. 339. *)
Lemma restricted_subspace_forward_linear:linear restricted_subspace_forward.
Proof. by move=>a x y;apply:val_inj. Qed.
HB.instance Definition _:=GRing.isLinear.Build R SCR SR *:%R
  restricted_subspace_forward restricted_subspace_forward_linear.

(** Source for [restricted_subspace_backward_linear]: real linearity
    of the inverse carrier identification in 3.4.12, p. 339. *)
Lemma restricted_subspace_backward_linear:linear restricted_subspace_backward.
Proof. by move=>a x y;apply:val_inj. Qed.
HB.instance Definition _:=GRing.isLinear.Build R SR SCR *:%R
  restricted_subspace_backward restricted_subspace_backward_linear.

(** Source for [restricted_subspace_forwardK]: the actual
    carrier identification has its original inverse, supporting
    3.4.12, p. 339. *)
Lemma restricted_subspace_forwardK:cancel restricted_subspace_forward restricted_subspace_backward.
Proof. by move=>x;apply:val_inj. Qed.

(** Source for [restricted_subspace_backwardK]: the reverse
    carrier identity for the real plane in 3.4.12,
    p. 339. *)
Lemma restricted_subspace_backwardK:cancel restricted_subspace_backward restricted_subspace_forward.
Proof. by move=>x;apply:val_inj. Qed.

(** Source for [complex_plane_real_basis]: every original
    complex m-basis gives an actual real 2m-basis,
    3.4.12, p. 339; reuse the ordered
    paired basis of 1.6.6, p. 26. *)
Theorem complex_plane_real_basis m (e:'I_m->SC):is_basis e ->
  is_basis (fun j=>restricted_subspace_forward (ordered_real_basis e j)).
Proof.
move=>he;exact:(@basis_transport R (Choice.clone 'I_(m+m) _) SCR SR
  (ordered_real_basis e)
  (GRing.Linear.clone _ _ _ _ restricted_subspace_forward _)
  (GRing.Linear.clone _ _ _ _ restricted_subspace_backward _)
  restricted_subspace_forwardK restricted_subspace_backwardK (ordered_real_basisP he)).
Qed.
End Subspace.

(** Source for [complex_grassmann_real]: an original member
    of G(C^n,m) gives a member of G(R^(2n),2m)
    with precisely the same vectors, 3.4.12, p. 339.
    This statement includes m=0. *)
Theorem complex_grassmann_real (R:realFieldType)
    (X:lmodType (ComplexScalars.C R)) m (Z:G X m):
  exists W:G (restricted_space (ComplexScalars.embed R) X) (m+m),
    forall x,grassmann_val W x <->grassmann_val Z x.
Proof.
have [e he]:=grassmann_proof Z.
have hReal:=complex_plane_real_basis he.
exists (@GrassmannSubspace R (restricted_space (ComplexScalars.embed R) X)
  (m+m) (restricted_complex_subspace (grassmann_val Z)) (ex_intro _ _ hReal)).
by move=>x.
Qed.
