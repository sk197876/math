(** Federer (1969), 2.5.11, p. 102: the cardinal arithmetic of the example.
    The measures beta_j are countably subadditive because a countable union
    of sets of cardinal less than aleph_j has cardinal less than aleph_j,
    and the final estimate uses card{(u,v): k(u,v) <= 0} <= (card Y_1) times
    aleph-one = aleph-one. Kelley, General Topology, Appendix, Theorems
    179-180, pp. 279-280 (Dover 2017 reprint of 1955), give the general
    product law. All consequences below use only the sealed square law. *)
From mathcomp Require Import all_boot boolp classical_sets functions cardinality.
From Federer Require Import CardinalSuccessorUP CardinalInjection AlephOneSquareSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.

(** Source for [aleph_one_square]: public form of the equation
    (card Y_1) times aleph-one equals aleph-one in Federer 2.5.11,
    p. 102, for a representative of the successor of aleph-zero. *)
Theorem aleph_one_square (J : choiceType) (Y : set J) :
  is_cardinal_successor (@setT nat) Y -> Y `*` Y #<= Y.
Proof. exact: AlephOneSquare.square_bound. Qed.

(** Source for [card_le_setX]: supporting monotonicity of the
    Cartesian product under cardinal comparison, Kelley, Appendix,
    Theorem 180, p. 280, used for Federer 2.5.11, p. 102. *)
Lemma card_le_setX (I J K L : choiceType) (A : set I) (A' : set J)
    (B : set K) (B' : set L) :
  A #<= A' -> B #<= B' -> A `*` B #<= A' `*` B'.
Proof.
move=> hA hB.
case: (pselect (exists a, A a))=> [[a ha]|hA0]; last first.
  have -> : A `*` B = set0.
    by apply/seteqP; split=> // p [hp _]; apply: hA0; exists p.1.
  exact: card_ge0.
case: (pselect (exists b, B b))=> [[b hb]|hB0]; last first.
  have -> : A `*` B = set0.
    by apply/seteqP; split=> // p [_ hp]; apply: hB0; exists p.2.
  exact: card_ge0.
have [a' ha'] : exists a', A' a'.
  apply: contrapT=> hn.
  have hA' : A' = set0 by apply/seteqP; split=> // x hx; apply: hn; exists x.
  by move: hA; rewrite hA'=> /card_le0P hA0; rewrite hA0 in ha.
have [b' hb'] : exists b', B' b'.
  apply: contrapT=> hn.
  have hB' : B' = set0 by apply/seteqP; split=> // x hx; apply: hn; exists x.
  by move: hB; rewrite hB'=> /card_le0P hB0; rewrite hB0 in hb.
have [e [he hei]] := cardinal_injection_with_default a' hA.
have [g [hg hgi]] := cardinal_injection_with_default b' hB.
apply: (@cardinal_bound_of_injection _ _ (A `*` B) (A' `*` B') (fun p => (e p.1, g p.2))).
- move=> p [h1 h2]; split; [exact: he|exact: hg].
- move=> [x y] [z w] /set_mem [hx hy] /set_mem [hz hw] /= [h1 h2].
  have -> : x = z by exact: hei _ _ (mem_set hx) (mem_set hz) h1.
  by have -> : y = w by exact: hgi _ _ (mem_set hy) (mem_set hw) h2.
Qed.

(** Source for [cardinal_bigcup_product_bound]: supporting bound of
    an indexed union by the product of the index set with a common
    bound, Kelley, Appendix, Theorem 180, p. 280, used for
    Federer 2.5.11, p. 102. *)
Lemma cardinal_bigcup_product_bound (I K T : choiceType) (D : set I)
    (F : I -> set T) (P : set K) :
  (forall i, D i -> F i #<= P) -> \bigcup_(i in D) F i #<= D `*` P.
Proof.
move=> hF.
case: (pselect (exists p, P p))=> [[d hd]|hP0]; last first.
  have hP : P = set0 by apply/seteqP; split=> // p hp; apply: hP0; exists p.
  have -> : \bigcup_(i in D) F i = set0.
    apply/seteqP; split=> // x [i hi hx].
    by have := hF i hi; rewrite hP=> /card_le0P h; rewrite h in hx.
  exact: card_ge0.
case: (pselect (exists i, D i))=> [[i0 hi0]|hD0]; last first.
  have -> : \bigcup_(i in D) F i = set0.
    by apply/seteqP; split=> // x [i hi _]; apply: hD0; exists i.
  exact: card_ge0.
pose e := fun i => if pselect (D i) is left h then
  sval (cid (cardinal_injection_with_default d (hF i h))) else fun _ : T => d.
have he : forall i, D i -> set_fun (F i) P (e i) /\ set_inj (F i) (e i).
  move=> i hi; rewrite /e; case: pselect=> [h|//].
  exact: svalP (cid (cardinal_injection_with_default d (hF i h))).
pose idx := fun x => if pselect (exists i, D i /\ F i x) is left h then sval (cid h) else i0.
have hidx : forall x, (\bigcup_(i in D) F i) x -> D (idx x) /\ F (idx x) x.
  move=> x [i hi hx]; rewrite /idx; case: pselect=> [h|hn].
  - exact: svalP (cid h).
  - by case: hn; exists i.
apply: (@cardinal_bound_of_injection _ _ _ _ (fun x => (idx x, e (idx x) x))).
- move=> x hx; have [h1 h2] := hidx x hx; split=> //.
  exact: (he _ h1).1.
- move=> x y /set_mem hx /set_mem hy [h1 h2].
  have [hx1 hx2] := hidx x hx; have [hy1 hy2] := hidx y hy.
  rewrite -h1 in h2 hy2.
  exact: (he _ hx1).2 _ _ (mem_set hx2) (mem_set hy2) h2.
Qed.

(** Source for [aleph_one_countable_union_bound]: countable unions of
    sets of cardinal at most aleph-one have cardinal at most aleph-one,
    the subadditivity requirement for beta_2 in Federer 2.5.11, p. 102;
    Kelley, Appendix, Theorem 180, p. 280. *)
Theorem aleph_one_countable_union_bound (J K : choiceType) (Y : set J)
    (D : set (set K)) :
  is_cardinal_successor (@setT nat) Y -> countable D ->
  (forall B, D B -> B #<= Y) -> \bigcup_(B in D) B #<= Y.
Proof.
move=> hY hD hB.
have h1 := @cardinal_bigcup_product_bound _ _ _ D id Y hB.
have h2 : D `*` Y #<= Y `*` Y by apply: card_le_setX=> //; exact: card_le_trans hD hY.1.
exact: card_le_trans h1 (card_le_trans h2 (aleph_one_square hY)).
Qed.

(** Source for [aleph_one_section_bound]: the estimate
    card{(u,v): k(u,v) <= 0} <= (card Y_1) times aleph-one = aleph-one
    in Federer 2.5.11, p. 102: a set of pairs whose vertical sections
    have cardinal at most aleph-one, indexed by a set of cardinal at
    most aleph-one, has cardinal at most aleph-one. *)
Theorem aleph_one_section_bound (I J K : choiceType) (Y : set J)
    (S : set (I * K)) :
  is_cardinal_successor (@setT nat) Y -> (@setT I) #<= Y ->
  (forall u, [set v | S (u, v)] #<= Y) -> S #<= Y.
Proof.
move=> hY hI hS.
have hsub : S `<=` \bigcup_(u in @setT I) ([set u] `*` [set v | S (u, v)]).
  by move=> [u v] huv; exists u=> //; split.
have hsec : forall u, (@setT I) u -> [set u] `*` [set v | S (u, v)] #<= Y.
  move=> u _; apply: card_le_trans (hS u).
  apply: (@cardinal_bound_of_injection _ _ _ _ snd).
  - by move=> p [_ hp].
  - by move=> [a b] [c d] /set_mem [/= -> _] /set_mem [/= -> _] /= ->.
have h1 := @cardinal_bigcup_product_bound _ _ _ (@setT I) _ Y hsec.
have h2 : (@setT I) `*` Y #<= Y `*` Y by apply: card_le_setX.
exact: card_le_trans (subset_card_le hsub)
  (card_le_trans h1 (card_le_trans h2 (aleph_one_square hY))).
Qed.
