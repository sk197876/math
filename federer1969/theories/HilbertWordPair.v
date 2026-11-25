(** Federer (1969), 1.10.5, p. 48: supporting equality of two entries of a
    secondary maximizing tuple. The scalar two-slot slice and its norm bound
    are derived from the original symmetric form, then the proved Hilbert
    extremal-pair argument applies. This is local proof infrastructure *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import InnerProductUP InnerNorm LinearBasis SymmetricForms
  SymmetricFormWords RealNormUP SymmetricFormListSlots HilbertFormCompactness
  HilbertWordMaximum HilbertExtremalPair.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Pair.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Local Notation N := (inner_norm hB).
Variable m : nat.
Variable f : S_m V R^o m.
Local Notation F := (sform_words f).
Variable M : R.
Hypothesis hmax : forall r, size r=m -> (forall v, v\in r -> N v<= 1) -> `|F r|<=M.

(** Source for [hilbert_word_extremal_front_equal]: Federer
    1.10.5, p. 48, supporting equality of the first two
    entries of a secondary maximizing word. Every entry is assumed
    unit; this hypothesis is supplied by positive-maximum saturation. *)
Theorem hilbert_word_extremal_front_equal x y s :
  size (x::y::s)=m -> (forall v, v\in x::y::s -> N v= 1) ->
  `|F (x::y::s)|=M ->
  (forall r, size r=m -> (forall v, v\in r -> N v<= 1) -> `|F r|=M ->
    N (\sum_(v<-r) v)<=N (\sum_(v<-x::y::s) v)) -> x=y.
Proof.
move=> hs hu he hsecondary.
pose g (u v:V) := F (u::v::s).
have hg : is_symmetric_bilinear g := symmetric_form_front_symmetric f s.
have hL := @hilbert_word_maximum_operator_bound R V B hB m f M hmax.
have hr : forall v, v\in s -> N v= 1.
  move=> v hv; apply: hu; by rewrite !in_cons hv !orbT.
have hprod : (\prod_(v<-s) N v)= 1.
  apply: big1_seq=> v hv; exact: hr hv.
have hb : forall u v, `|g u v|<=M*N u*N v.
  move=> u v.
  have hlen : size (u::v::s)=m := hs.
  have hh := @symmetric_form_word_norm_bound R V R^o N (fun r:R=>`|r|)
    (inner_norm_real_norm hB) (proj1 (scalar_absolute_value_norm R)) m f M hL
    (u::v::s) hlen.
  rewrite !big_cons hprod mulr1 mulrA in hh; exact hh.
have hx : N x= 1 := hu x (mem_head _ _).
have hy : N y= 1 by apply: hu; rewrite !in_cons eqxx !orbT.
apply: (@hilbert_extremal_pair_equal R V B hB g hg M hb
  (\sum_(v<-s) v) x y hx hy he)=> u v hnu hnv hgv.
have hlen : size (u::v::s)=m := hs.
have hunit : forall w, w\in u::v::s -> N w<= 1.
  move=> w; rewrite !in_cons=> /orP[/eqP ->|/orP[/eqP ->|hw]].
  - by rewrite hnu.
  - by rewrite hnv.
  - by rewrite (hr _ hw).
have hh := hsecondary (u::v::s) hlen hunit hgv.
rewrite !big_cons !addrA in hh.
rewrite [(_+(u+v))]addrC [(_+(x+y))]addrC; exact hh.
Qed.
End Pair.
