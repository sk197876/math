(** Federer (1969), 3.1.11, pp. 218–219:
    argument splitting for the recursive higher differential.
    These finite-family identities support the identification
    of (k+1)-linear maps with linear maps into k-linear maps. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import FamilyUpdate ConcatenatedFamilies TensorFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [multilinear_arguments_join]: grouping consecutive
    arguments of higher differentials, Federer 3.1.11, p. 219.
    Auxiliary notation, including empty argument blocks. *)
Definition multilinear_arguments_join (T : Type) m n
    (u : {ffun 'I_m->T}) (v : {ffun 'I_n->T}) : {ffun 'I_(m+n)->T} :=
  [ffun i=>concatenate_family u v i].

(** Source for [multilinear_arguments_left]: the first block
    of arguments in the recursive differential of Federer
    3.1.11, p. 219. Auxiliary notation. *)
Definition multilinear_arguments_left (T : Type) m n
    (u : {ffun 'I_(m+n)->T}) : {ffun 'I_m->T} :=
  [ffun i=>u (lshift n i)].

(** Source for [multilinear_arguments_right]: the last block
    of arguments in the recursive differential of Federer
    3.1.11, p. 219. Auxiliary notation. *)
Definition multilinear_arguments_right (T : Type) m n
    (u : {ffun 'I_(m+n)->T}) : {ffun 'I_n->T} :=
  [ffun i=>u (rshift m i)].

(** Source for [multilinear_arguments_join_left]: first-block
    evaluation supporting the recursive identification in
    Federer 3.1.11, p. 219. *)
Lemma multilinear_arguments_join_left (T : Type) m n
    (u : {ffun 'I_m->T}) (v : {ffun 'I_n->T}) i :
  multilinear_arguments_join u v (lshift n i)=u i.
Proof. by rewrite /multilinear_arguments_join ffunE concatenate_family_l. Qed.

(** Source for [multilinear_arguments_join_right]: last-block
    evaluation supporting the recursive identification in
    Federer 3.1.11, p. 219. *)
Lemma multilinear_arguments_join_right (T : Type) m n
    (u : {ffun 'I_m->T}) (v : {ffun 'I_n->T}) i :
  multilinear_arguments_join u v (rshift m i)=v i.
Proof. by rewrite /multilinear_arguments_join ffunE concatenate_family_r. Qed.

(** Source for [multilinear_arguments_join_split]: recombining
    the argument blocks loses no information, supporting
    Federer 3.1.11, p. 219. *)
Lemma multilinear_arguments_join_split (T : Type) m n
    (u : {ffun 'I_(m+n)->T}) :
  multilinear_arguments_join (multilinear_arguments_left u)
    (multilinear_arguments_right u)=u.
Proof.
apply/ffunP=> i; case: (split_ordP i)=> j ->.
- by rewrite multilinear_arguments_join_left /multilinear_arguments_left ffunE.
- by rewrite multilinear_arguments_join_right /multilinear_arguments_right ffunE.
Qed.

(** Source for [multilinear_arguments_left_join]: recovering
    the first argument block, supporting Federer 3.1.11,
    p. 219. *)
Lemma multilinear_arguments_left_join (T : Type) m n
    (u : {ffun 'I_m->T}) (v : {ffun 'I_n->T}) :
  multilinear_arguments_left (multilinear_arguments_join u v)=u.
Proof. by apply/ffunP=> i; rewrite /multilinear_arguments_left ffunE multilinear_arguments_join_left. Qed.

(** Source for [multilinear_arguments_right_join]: recovering
    the last argument block, supporting Federer 3.1.11,
    p. 219. *)
Lemma multilinear_arguments_right_join (T : Type) m n
    (u : {ffun 'I_m->T}) (v : {ffun 'I_n->T}) :
  multilinear_arguments_right (multilinear_arguments_join u v)=v.
Proof. by apply/ffunP=> i; rewrite /multilinear_arguments_right ffunE multilinear_arguments_join_right. Qed.

(** Source for [multilinear_arguments_join_with_left]:
    a change in one first-block argument is the corresponding
    change in the joined tuple, supporting multilinearity
    in Federer 3.1.11, p. 219. *)
Lemma multilinear_arguments_join_with_left (T : Type) m n
    (u : {ffun 'I_m->T}) (v : {ffun 'I_n->T}) (i : 'I_m) (x : T) :
  multilinear_arguments_join (@family_with m (fun _=>T) u i x) v=
    @family_with (m+n) (fun _=>T) (multilinear_arguments_join u v) (lshift n i) x.
Proof.
apply/ffunP=> j; case: (split_ordP j)=> k ->.
- rewrite multilinear_arguments_join_left.
  case: (eqVneq i k)=> [<-|hik].
  + by rewrite !family_with_in.
  + by rewrite !family_with_out ?eq_lshift // multilinear_arguments_join_left.
- by rewrite family_with_out ?eq_lrshift // !multilinear_arguments_join_right.
Qed.

(** Source for [multilinear_arguments_join_with_right]:
    a change in one last-block argument is the corresponding
    change in the joined tuple, supporting multilinearity
    in Federer 3.1.11, p. 219. *)
Lemma multilinear_arguments_join_with_right (T : Type) m n
    (u : {ffun 'I_m->T}) (v : {ffun 'I_n->T}) (i : 'I_n) (x : T) :
  multilinear_arguments_join u (@family_with n (fun _=>T) v i x)=
    @family_with (m+n) (fun _=>T) (multilinear_arguments_join u v) (rshift m i) x.
Proof.
apply/ffunP=> j; case: (split_ordP j)=> k ->.
- by rewrite family_with_out ?eq_rlshift // !multilinear_arguments_join_left.
- rewrite multilinear_arguments_join_right.
  case: (eqVneq i k)=> [<-|hik].
  + by rewrite !family_with_in.
  + by rewrite !family_with_out ?eq_rshift // multilinear_arguments_join_right.
Qed.

(** Source for [multilinear_arguments_product]: the homogeneous
    product of factor norms splits with the argument blocks.
    Supporting the normed-space identification in Federer
    3.1.11, p. 219. *)
Lemma multilinear_arguments_product (K : comPzRingType) (T : Type) m n
    (N : T->K) (u : {ffun 'I_m->T}) (v : {ffun 'I_n->T}) :
  \prod_(i<m+n) N (multilinear_arguments_join u v i)=
    (\prod_(i<m) N (u i))*(\prod_(i<n) N (v i)).
Proof.
rewrite big_split_ord; congr (_*_); apply: eq_bigr=> i _;
  by rewrite ?multilinear_arguments_join_left ?multilinear_arguments_join_right.
Qed.

(** Source for [multilinear_arguments_fixed_right]:
    fixing the last arguments preserves multilinearity in
    the first arguments, Federer 3.1.11, p. 219. *)
Lemma multilinear_arguments_fixed_right (K : fieldType) m n
    (X Y : lmodType K) (f : {ffun 'I_(m+n)->X}->Y) :
  multilinear f -> forall v : {ffun 'I_n->X},
    multilinear (fun u : {ffun 'I_m->X}=>f (multilinear_arguments_join u v)).
Proof.
move=> hf v u i c x y.
by rewrite !multilinear_arguments_join_with_left; exact: hf.
Qed.

(** Source for [multilinear_arguments_fixed_left]:
    fixing the first arguments preserves multilinearity in
    the last arguments, Federer 3.1.11, p. 219. *)
Lemma multilinear_arguments_fixed_left (K : fieldType) m n
    (X Y : lmodType K) (f : {ffun 'I_(m+n)->X}->Y) :
  multilinear f -> forall u : {ffun 'I_m->X},
    multilinear (fun v : {ffun 'I_n->X}=>f (multilinear_arguments_join u v)).
Proof.
move=> hf u v i c x y.
by rewrite !multilinear_arguments_join_with_right; exact: hf.
Qed.
