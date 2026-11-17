(** Federer (1969), 3.4.12, p. 338:
    symmetry transfers a scalar law in one actual
    derivative argument to every argument. This finite
    permutation connection reuses the project's actual tuple
    replacement and permutation operations. *)
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From Federer Require Import FamilyUpdate FiniteArgumentPermutation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

(** Source for [argument_permutation_replacement]: moving the
    replaced slot through an actual transposition, supporting
    the higher complex-linearity assertion of 3.4.12, p. 338. *)
Lemma argument_permutation_replacement (T:Type) k (u:{ffun 'I_k->T})
    (i j:'I_k) (x:T):
  finite_argument_permutation (tperm i j) (@family_with k (fun _=>T) u i x)=
    @family_with k (fun _=>T) (finite_argument_permutation (tperm i j) u) j x.
Proof.
apply/ffunP=>l;rewrite /finite_argument_permutation ffunE.
case:(eqVneq l j)=>[->|hDifferent].
- by rewrite tpermR !family_with_in.
- have hOther:i!=tperm i j l.
    rewrite -{1}(tpermR i j) (inj_eq (perm_inj (s:=tperm i j))).
    by rewrite eq_sym.
  have hJL:j!=l by rewrite eq_sym.
  by rewrite !family_with_out ?hOther ?hJL // /finite_argument_permutation ffunE.
Qed.

(** Source for [symmetric_scalar_slot_transfer]: an actual
    symmetric form's scalar identity in one chosen slot
    holds in every slot, as used for complex
    higher differentials in 3.4.12, p. 338.
    The scalar and target operations remain arbitrary maps. *)
Theorem symmetric_scalar_slot_transfer (T U:Type) k
    (F:{ffun 'I_k->T}->U) (a:'I_k) (P:T->T) (Q:U->U):
  (forall s u,F (finite_argument_permutation s u)=F u) ->
  (forall u x,F (@family_with k (fun _=>T) u a (P x))=
    Q (F (@family_with k (fun _=>T) u a x))) ->
  forall u (i:'I_k) x,F (@family_with k (fun _=>T) u i (P x))=
    Q (F (@family_with k (fun _=>T) u i x)).
Proof.
move=>hSymmetric hFirst u i x.
have hLeft:=hSymmetric (tperm i a) (@family_with k (fun _=>T) u i (P x)).
have hRight:=hSymmetric (tperm i a) (@family_with k (fun _=>T) u i x).
rewrite argument_permutation_replacement in hLeft.
rewrite argument_permutation_replacement in hRight.
exact:(eq_trans (esym hLeft)
  (eq_trans (hFirst (finite_argument_permutation (tperm i a) u) x)
    (congr1 Q hRight))).
Qed.
