(** Federer (1969), 2.10.24(2), p. 188: supporting finite weighted-layer
    argument. Federer first reduces rational weights to integers and removes
    one disjoint layer at a time. Here a layer removes the least selected
    real weight, stopping at the target threshold. A weight vanishes at each
    unfinished step, so finite-set induction proves the same cost estimate
    directly for real weights. This is an explicit departure in proof route,
    preserving the displayed layer accounting. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality reals lra ring.
From Federer Require Import FiniteRealMaximum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_layer_subfamily_sum]: supporting
    finite subfamily bookkeeping for the double sums
    in 2.10.24(2), p. 188. Terms outside the
    selected subfamily are extended by zero. *)
Lemma finite_layer_subfamily_sum (R : realType) (J : choiceType)
    (P H : {fset J}) (f : J -> R) :
  (H `<=` P)%fset ->
  \sum_(j <- H) f j=\sum_(j <- P) (if j \in H then f j else 0).
Proof.
move=> hHP.
have heq : \sum_(j <- H) (if j \in H then f j else 0)=
    \sum_(j <- P) (if j \in H then f j else 0).
  apply: big_fset_incl; first exact hHP.
  by move=> j hj hjnot; rewrite (negbTE hjnot).
rewrite -heq; apply: eq_big_seq=> j hj; by rewrite hj.
Qed.

(** Source for [finite_disjoint_indicator_bound]: supporting
    fact that removing one disjoint layer lowers each
    pointwise weighted multiplicity by at most its weight,
    as used in 2.10.24(2), p. 188. *)
Lemma finite_disjoint_indicator_bound (R : realType) (X J : choiceType)
    (S : J -> set X) (H : {fset J}) (a : R) x :
  0<=a -> (forall i j, i \in H -> j \in H -> i!=j -> S i `&` S j=set0) ->
  \sum_(j <- H) (if x \in S j then a else 0)<=a.
Proof.
move=> ha hd.
case: (pselect (exists i, i \in H /\ S i x))=> [[i [hi hxi]]|hnone].
- rewrite (big_fsetD1 _ hi) /= (mem_set hxi).
  have hz : \sum_(j <- (H `\ i)%fset) (if x \in S j then a else 0)=0.
    rewrite big_seq; apply: big1=> j; rewrite !inE=> /andP[hji hj].
    have hnot : ~ S j x.
      move=> hxj; have hbad : (S j `&` S i) x by split.
      by rewrite (hd j i hj hi hji) in hbad.
    have hnx : x \notin S j by apply/negP=> /set_mem hxjnew; exact: hnot hxjnew.
    by rewrite (negbTE hnx).
  by rewrite hz addr0.
- have hz : \sum_(j <- H) (if x \in S j then a else 0)=0.
    rewrite big_seq; apply: big1=> j hj.
    have hnot : ~ S j x by move=> hx; apply: hnone; exists j; split.
    have hnx : x \notin S j by apply/negP=> /set_mem hxjnew; exact: hnot hxjnew.
    by rewrite (negbTE hnx).
  by rewrite hz.
Qed.

(** Source for [finite_weighted_disjoint_layer_bound]: supporting
    real-weight version of the last displayed estimate
    in 2.10.24(2), p. 188. The hypothesis
    supplies a disjoint layer and its unweighted cost
    bound for every remaining finite cover. Peeling
    the least selected weight proves the full fractional
    bound without rational approximation. No geometric
    selection or measure law is assumed as an axiom. *)
Theorem finite_weighted_disjoint_layer_bound (R : realType) (X J : choiceType)
    (S : J -> set X) (F : set J) (A : set X) (cost : J -> R) (b : R) :
  A!=set0 -> 0<=b -> (forall j, F j -> 0<=cost j) ->
  (forall P : {fset J}, (forall j, j \in P -> F j) -> A `<=` \bigcup_(j in [set` P]) S j ->
    exists H : {fset J}, (H `<=` P)%fset /\ H!=fset0 /\
      (forall i j, i \in H -> j \in H -> i!=j -> S i `&` S j=set0) /\ b<=\sum_(j <- H) cost j) ->
  forall (P : {fset J}) (v : J -> R) (t : R),
    (forall j, j \in P -> F j) -> (forall j, j \in P -> 0<=v j) -> 0<t ->
    (forall x, A x -> t<=\sum_(j <- P) (if x \in S j then v j else 0)) ->
    t*b<=\sum_(j <- P) v j*cost j.
Proof.
move=> hA hb hc hselect P; elim/finSet_rect: P=> P IH v t hPF hv ht hlevel.
have hremove i (hi : i \in P) : forall j, j \in (P `\ i)%fset -> F j.
  by move=> j; rewrite !inE=> /andP[_ hj]; exact: hPF.
case: (pselect (exists i, i \in P /\ v i=0))=> [[i [hi hvi]]|hnzero].
- have hsub := fproperD1 hi.
  have hnewlevel x (hx : A x) : t<=\sum_(j <- (P `\ i)%fset) (if x \in S j then v j else 0).
    have hh := hlevel x hx; rewrite (big_fsetD1 _ hi) /= hvi in hh.
    by case: ifP=> _ in hh; rewrite add0r in hh.
  have hrest j : j \in (P `\ i)%fset -> 0<=v j.
    move=> hj; move: hj; rewrite !inE=> /andP[_ hj]; exact: hv.
  have hh := IH _ hsub v t (hremove i hi) hrest ht hnewlevel.
  by rewrite (big_fsetD1 _ hi) /= hvi mul0r add0r.
have hvpos j (hj : j \in P) : 0<v j.
  rewrite lt_neqAle (hv j hj) andbT; apply/eqP=> he; apply: hnzero.
  exists j; split=> //; exact: esym he.
have hcover : A `<=` \bigcup_(j in [set` P]) S j.
  move=> x hx; apply: contrapT=> hnone.
  have hz : \sum_(j <- P) (if x \in S j then v j else 0)=0.
    rewrite big_seq; apply: big1=> j hj.
    have hnot : ~ S j x by move=> hxj; apply: hnone; exists j.
    have hnx : x \notin S j by apply/negP=> /set_mem hxjnew; exact: hnot hxjnew.
    by rewrite (negbTE hnx).
  have hh := hlevel x hx; by rewrite hz leNgt ht in hh.
have [H [hHP [hHne [hdisj hbc]]]] := hselect P hPF hcover.
have hHset : [set` H]!=set0.
  apply: contrapT=> hnone; apply: (negP hHne); apply/eqP/fsetP=> j.
  rewrite in_fset0; apply/negP=> hj; apply: hnone; by exists j.
have [i [hi hmin]] := @finite_nonempty_real_maximum R J [set` H] (fun j=> -v j)
  (finite_fset _) hHset.
have hiH : i \in H := hi.
have hiP := (fsubsetP hHP) i hiH.
have hvi := hvpos i hiP.
have hleast j (hj : j \in H) : v i<=v j by have := hmin j hj; rewrite lerN2.
case: (leP t (v i))=> hti.
- apply: le_trans (ler_wpM2l (ltW ht) hbc) _.
  rewrite big_distrr /= (finite_layer_subfamily_sum _ hHP).
  rewrite !big_seq; apply: ler_sum=> j hj; case: ifP=> hjH.
  + have hcoef := hc j (hPF j hj).
    have hle := le_trans hti (hleast j hjH).
    nra.
  + exact: mulr_ge0 (hv j hj) (hc j (hPF j hj)).
- pose a := v i.
  pose w j := if j \in H then v j-a else v j.
  have hw j (hj : j \in P) : 0<=w j.
    rewrite /w; case: ifP=> hjH; [by rewrite subr_ge0; exact: hleast|exact: hv].
  have hwi : w i=0 by rewrite /w hiH /a subrr.
  have hdecomp x :
      \sum_(j <- P) (if x \in S j then v j else 0)=
      \sum_(j <- P) (if x \in S j then w j else 0)+
      \sum_(j <- H) (if x \in S j then a else 0).
    have hH := finite_layer_subfamily_sum (fun j=>if x \in S j then a else 0) hHP.
    rewrite hH -big_split /=; apply: eq_big_seq=> j hj.
    rewrite /w; by case: ifP=> hjH; case: ifP=> hx; lra.
  have hnewlevel x (hx : A x) :
      t-a<=\sum_(j <- (P `\ i)%fset) (if x \in S j then w j else 0).
    have hdrop := @finite_disjoint_indicator_bound R X J S H a x (ltW hvi) hdisj.
    have hh := hlevel x hx; rewrite hdecomp (big_fsetD1 _ hiP) /= hwi in hh.
    case: ifP=> hxi in hh; rewrite add0r in hh; lra.
  have hrest j : j \in (P `\ i)%fset -> 0<=w j.
    move=> hj; move: hj; rewrite !inE=> /andP[_ hj]; exact: hw.
  have hta : 0<t-a by rewrite /a; lra.
  have hsum := IH _ (fproperD1 hiP) w (t-a) (hremove i hiP) hrest hta hnewlevel.
  have hsmall := ler_wpM2l (ltW hvi) hbc.
  have hcost : \sum_(j <- P) v j*cost j=
      \sum_(j <- (P `\ i)%fset) w j*cost j+a*\sum_(j <- H) cost j.
    have hz : \sum_(j <- P) w j*cost j=\sum_(j <- (P `\ i)%fset) w j*cost j.
      by rewrite (big_fsetD1 _ hiP) /= hwi mul0r add0r.
    rewrite -hz big_distrr /=.
    have hH := finite_layer_subfamily_sum (fun j=>a*cost j) hHP.
    rewrite hH -big_split /=; apply: eq_big_seq=> j hj.
    rewrite /w; case: ifP=> _; ring.
  rewrite hcost; have hh := lerD hsum hsmall; rewrite /a in hh *; nra.
Qed.
