(** Federer (1969), 3.1.1(4), p. 210: algebraic identities supporting
    the derivative of a continuous multilinear map. The factors are the
    arbitrary vector spaces of 1.1.1, p. 8; they need not coincide or have
    finite dimension. These are supporting identities, not additional
    claims attributed to the printed paragraph. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import Hom TensorFamilyUP FamilyUpdate.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Algebra.
Variable K : fieldType.
Variable m : nat.
Variable V : 'I_m -> lmodType K.
Variable Y : lmodType K.
Variable f : {dffun forall i, V i} -> Y.
Hypothesis hf : multilinear f.

(** Source for [multilinear_family_scale]: homogeneity in one factor,
    from 1.1.1, p. 8, supporting the first-order expansion in
    Federer 3.1.1(4), p. 210. *)
Lemma multilinear_family_scale x i (c : K) (v : V i) :
  f (family_with x (c *: v)) = c *: f (family_with x v).
Proof.
pose L := @HomMap K (V i) Y (fun v => f (family_with x v))
  (introT (asboolP _) (@hf x i)).
change (L (c *: v) = c *: L v); exact: linearZ.
Qed.

(** Source for [multilinear_family_subtract]: subtraction in one
    factor, from 1.1.1, p. 8, supporting the finite telescoping
    expansion used for Federer 3.1.1(4), p. 210. *)
Lemma multilinear_family_subtract x i (v w : V i) :
  f (family_with x (v-w)) = f (family_with x v)-f (family_with x w).
Proof.
pose L := @HomMap K (V i) Y (fun v => f (family_with x v))
  (introT (asboolP _) (@hf x i)).
change (L (v-w) = L v-L w); exact: linearB.
Qed.

(** Source for [multilinear_family_zero]: a zero factor makes a
    multilinear value zero, supporting the degenerate cases of
    Federer 3.1.1(4), p. 210. *)
Lemma multilinear_family_zero x i : f (family_with x (0 : V i)) = 0.
Proof.
by rewrite -(scale0r (0 : V i)) multilinear_family_scale scale0r.
Qed.
End Algebra.

(** Source for [family_prefix_mix]: auxiliary coordinate path for
    the finite multilinear expansion of Federer 3.1.1(4), p. 210.
    Its first k factors are taken from y and its remaining factors
    from x. The definition also covers the empty product. *)
Definition family_prefix_mix m (V : 'I_m -> Type)
    (x y : {dffun forall i, V i}) (k : nat) : {dffun forall i, V i} :=
  [ffun i : 'I_m => if (i<k)%N then y i else x i].

(** Source for [family_prefix_mix_zero]: initial endpoint of the
    supporting multilinear path for Federer 3.1.1(4), p. 210. *)
Lemma family_prefix_mix_zero m (V : 'I_m -> Type)
    (x y : {dffun forall i, V i}) : family_prefix_mix x y 0=x.
Proof. by apply/ffunP=> i; rewrite /family_prefix_mix ffunE ltn0. Qed.

(** Source for [family_prefix_mix_full]: final endpoint of the
    supporting multilinear path for Federer 3.1.1(4), p. 210. *)
Lemma family_prefix_mix_full m (V : 'I_m -> Type)
    (x y : {dffun forall i, V i}) : family_prefix_mix x y m=y.
Proof. by apply/ffunP=> i; rewrite /family_prefix_mix ffunE ltn_ord. Qed.

(** Source for [family_prefix_mix_step]: consecutive tuples differ
    in exactly one factor in the supporting expansion of
    Federer 3.1.1(4), p. 210. *)
Lemma family_prefix_mix_step m (V : 'I_m -> Type)
    (x y : {dffun forall i, V i}) (i : 'I_m) :
  family_prefix_mix x y i.+1 = family_with (family_prefix_mix x y i) (y i).
Proof.
apply/ffunP=> j; case: (eqVneq i j)=> [<-|hij].
- by rewrite family_with_in /family_prefix_mix ffunE ltnSn.
- rewrite family_with_out // /family_prefix_mix !ffunE ltnS leq_eqVlt val_eqE.
  by rewrite eq_sym (negPf hij).
Qed.

(** Source for [multilinear_family_difference]: telescoping the
    changes in the m factors gives an exact increment formula,
    supporting the derivative asserted in Federer 3.1.1(4), p. 210. *)
Lemma multilinear_family_difference (K : fieldType) m
    (V : 'I_m -> lmodType K) (Y : lmodType K)
    (f : {dffun forall i, V i} -> Y) (hf : multilinear f)
    (x y : {dffun forall i, V i}) :
  f y-f x = \sum_(i<m)
    f (family_with (family_prefix_mix x y i) (y i-x i)).
Proof.
have ht := @telescope_sumr Y 0 m (fun k => f (family_prefix_mix x y k)) (leq0n m).
rewrite big_mkord family_prefix_mix_zero family_prefix_mix_full in ht.
rewrite -ht; apply: eq_bigr=> i _.
rewrite family_prefix_mix_step (multilinear_family_subtract hf).
congr (_-_); congr f.
have he : family_prefix_mix x y i i = x i.
  by rewrite /family_prefix_mix ffunE ltnn.
by rewrite -he family_with_id.
Qed.

(** Source for [multilinear_family_scale_subset]: independent
    homogeneity in a finite list of distinct factors, from 1.1.1,
    p. 8, supporting boundedness and differentiation in 3.1.1(4),
    p. 210. This auxiliary identity includes the empty list. *)
Lemma multilinear_family_scale_subset (K : fieldType) m
    (V : 'I_m -> lmodType K) (Y : lmodType K)
    (f : {dffun forall i, V i} -> Y) (hf : multilinear f)
    (x : {dffun forall i, V i}) (c : 'I_m -> K) (s : seq 'I_m) :
  uniq s ->
  f [ffun i : 'I_m => if i \in s then c i *: x i else x i] =
    (\prod_(i <- s) c i) *: f x.
Proof.
elim: s=> [|i s ih] /=.
- move=> _; rewrite big_nil scale1r; congr f.
  by apply/ffunP=> j; rewrite ffunE.
- move=> /andP [his hs]; rewrite big_cons.
  pose y := [ffun j : 'I_m => if j \in s then c j *: x j else x j].
  have he : [ffun j : 'I_m => if j \in i::s then c j *: x j else x j] =
      family_with y (c i *: x i).
    apply/ffunP=> j; case: (eqVneq i j)=> [<-|hij].
    + by rewrite family_with_in ffunE in_cons eqxx.
    + by rewrite family_with_out // /y !ffunE in_cons eq_sym (negPf hij).
  rewrite he (multilinear_family_scale hf).
  have hx : family_with y (x i)=y.
    have hy : y i=x i by rewrite /y ffunE (negPf his).
    by rewrite -hy family_with_id.
  by rewrite hx (ih hs) scalerA.
Qed.

(** Source for [multilinear_family_scale_all]: the product of the
    independent scalar factors multiplies a multilinear value,
    supporting the norm estimate for Federer 3.1.1(4), p. 210. *)
Lemma multilinear_family_scale_all (K : fieldType) m
    (V : 'I_m -> lmodType K) (Y : lmodType K)
    (f : {dffun forall i, V i} -> Y) (hf : multilinear f)
    (x : {dffun forall i, V i}) (c : 'I_m -> K) :
  f [ffun i : 'I_m => c i *: x i] = (\prod_(i<m) c i) *: f x.
Proof.
have h := @multilinear_family_scale_subset K m V Y f hf x c (index_enum 'I_m) (index_enum_uniq _).
have he : [ffun i : 'I_m => if i \in index_enum 'I_m then c i *: x i else x i] =
    [ffun i : 'I_m => c i *: x i].
  by apply/ffunP=> i; rewrite !ffunE mem_index_enum.
by rewrite he in h.
Qed.
