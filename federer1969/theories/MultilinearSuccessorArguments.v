(** Federer (1969), 3.1.11, p. 219:
    adjoining the last argument when the degree is written
    as a successor. The casts below transport along equality
    of natural-number dimensions only. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ConcatenatedFamilies MultilinearArguments.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [multilinear_arguments_cast]: reindexing the
    same finite argument family along an equality of its
    degree, supporting the recursion in Federer 3.1.11,
    p. 219. *)
Definition multilinear_arguments_cast (T : Type) m n (h : m=n)
    (u : {ffun 'I_m->T}) : {ffun 'I_n->T} :=
  [ffun i=>u (cast_ord (esym h) i)].

(** Source for [multilinear_arguments_cast_reflexive]:
    reflexive dimension transport leaves the arguments fixed,
    supporting Federer 3.1.11, p. 219. *)
Lemma multilinear_arguments_cast_reflexive (T : Type) m (h : m=m)
    (u : {ffun 'I_m->T}) : multilinear_arguments_cast h u=u.
Proof.
apply/ffunP=> i; rewrite /multilinear_arguments_cast ffunE.
congr (u _); exact: val_inj.
Qed.

(** Source for [multilinear_arguments_cast_inverse]:
    equality transport is reversible, supporting the recursive
    degree convention in Federer 3.1.11, p. 219. *)
Lemma multilinear_arguments_cast_inverse (T : Type) m n (h : m=n)
    (u : {ffun 'I_m->T}) :
  multilinear_arguments_cast (esym h) (multilinear_arguments_cast h u)=u.
Proof.
apply/ffunP=> i; rewrite /multilinear_arguments_cast !ffunE.
congr (u _); exact: val_inj.
Qed.

(** Source for [multilinear_successor_arguments]: append the
    last vector to the k earlier arguments, as in the recursive
    differential of Federer 3.1.11, p. 219. *)
Definition multilinear_successor_arguments (T : Type) k
    (u : {ffun 'I_k->T}) (x : T) : {ffun 'I_k.+1->T} :=
  multilinear_arguments_cast (addn1 k)
    (multilinear_arguments_join u [ffun i : 'I_1=>x]).

(** Source for [multilinear_successor_arguments_surjective]:
    every argument family has this earlier/last decomposition,
    supporting Federer 3.1.11, p. 219, even for k= 0. *)
Lemma multilinear_successor_arguments_surjective (T : Type) k
    (w : {ffun 'I_k.+1->T}) :
  exists u x, w=multilinear_successor_arguments u x.
Proof.
pose v := multilinear_arguments_cast (esym (addn1 k)) w.
exists (multilinear_arguments_left v), (multilinear_arguments_right v ord0).
rewrite /multilinear_successor_arguments.
have he : [ffun i : 'I_1=>multilinear_arguments_right v ord0]=
    multilinear_arguments_right v.
  by apply/ffunP=> i; rewrite ffunE (ord1 i).
rewrite he multilinear_arguments_join_split /v.
apply/ffunP=> i; rewrite /multilinear_arguments_cast !ffunE.
congr (w _); exact: val_inj.
Qed.

(** Source for [multilinear_successor_zero_arguments]:
    adjoining one vector to the empty family yields the
    unique one-entry family, supporting D^1 f=Df in
    Federer 3.1.11, pp. 218–219. *)
Lemma multilinear_successor_zero_arguments (T : Type)
    (u : {ffun 'I_0->T}) (x : T) :
  multilinear_successor_arguments u x=[ffun i : 'I_1=>x].
Proof.
apply/ffunP=> i; rewrite (ord1 i) /multilinear_successor_arguments
  /multilinear_arguments_cast ffunE.
have hi : cast_ord (esym (addn1 0)) ord0=rshift 0 ord0 by exact: val_inj.
by rewrite hi multilinear_arguments_join_right !ffunE.
Qed.


(** Source for [multilinear_arguments_cast_product]:
    transporting a finite degree does not change a
    product over its arguments, supporting the scalar-source
    formula in Federer 3.1.11, p. 220. *)
Lemma multilinear_arguments_cast_product (K : comPzRingType) (T : Type)
    m n (h : m=n) (N : T->K) (u : {ffun 'I_m->T}) :
  \prod_(i<n) N (multilinear_arguments_cast h u i)=\prod_(i<m) N (u i).
Proof. subst n; by rewrite multilinear_arguments_cast_reflexive. Qed.

(** Source for [multilinear_successor_product]:
    adjoining the last scalar factor multiplies the
    product by that factor, supporting the real-source
    higher differential in Federer 3.1.11, p. 220. *)
Lemma multilinear_successor_product (K : comPzRingType) k
    (u : {ffun 'I_k->K}) (t : K) :
  (\prod_(i<k.+1) multilinear_successor_arguments u t i)%R=
    ((\prod_(i<k) u i)*t)%R.
Proof.
rewrite /multilinear_successor_arguments.
have hh := @multilinear_arguments_cast_product K K (k+1) k.+1
  (addn1 k) (fun z : K=>z) (multilinear_arguments_join u [ffun i : 'I_1=>t]).
rewrite hh.
have hp := @multilinear_arguments_product K K k 1 (fun z : K=>z) u [ffun i : 'I_1=>t].
by rewrite hp big_ord1 ffunE.
Qed.


(** Source for [multilinear_successor_constant_arguments]:
    the tuple of k+1 equal arguments is obtained
    by adjoining one more equal argument, supporting
    the real-source coefficient formula in Federer
    3.1.11, p. 220. *)
Lemma multilinear_successor_constant_arguments (T : Type) k (t : T) :
  multilinear_successor_arguments [ffun i : 'I_k=>t] t=[ffun i : 'I_k.+1=>t].
Proof.
apply/ffunP=> i.
rewrite /multilinear_successor_arguments /multilinear_arguments_cast ffunE
  /multilinear_arguments_join ffunE /concatenate_family.
by case: split=> j; rewrite !ffunE.
Qed.
