(** Supporting numerical-sum step in Federer (1969), proof of 2.8.7, p. 144,
    last two paragraphs. A finite nonnegative sum has arbitrarily small
    remainders after removing a finite subfamily. We derive it from the
    local abstract finite- subsum and splitting laws, without importing
    summability. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_family_small_tail]: the choice of finite H with
    sum over G minus H less than epsilon in Federer 2.8.7, p. 144
    Countability is unnecessary for this auxiliary sum fact: the
    finite-subsum characterization suffices. *)
Theorem nonnegative_family_small_tail (R : realType) (I : choiceType)
    (D : set I) (f : I -> \bar R) (e : R) :
  (forall i, D i -> 0 <= f i) -> nonnegative_sum D f < +oo -> (0 < e)%R ->
  exists H, H `<=` D /\ finite_set H /\ nonnegative_sum (D `\` H) f < e%:E.
Proof.
move=> hnon hfinite he.
pose S := nonnegative_sum D f.
have hSf : S \is a fin_num by rewrite ge0_fin_numE //; exact: nonnegative_sum_nonnegative.
pose M := fine S.
have hSval : S = M%:E by rewrite /M fineK.
have ht : (M-e)%:E < S by rewrite hSval lte_fin ltrBlDr ltrDl.
have hex : exists B : {fset I}, (forall i, i \in B -> D i) /\
    (M-e)%:E < \sum_(i <- B) f i.
  case: (pselect (exists B : {fset I}, (forall i, i \in B -> D i) /\
      (M-e)%:E < \sum_(i <- B) f i))=> [h|hn]; first exact h.
  have hb (B : {fset I}) (hB : forall i, i \in B -> D i) :
      (\sum_(i <- B) f i) <= (M-e)%:E.
    rewrite leNgt; apply/negP=> hlt; apply: hn; by exists B.
  have hle : S <= (M-e)%:E := @nonnegative_sum_least R I D f (M-e)%:E hb.
  have hbad := le_lt_trans hle ht; by rewrite ltxx in hbad.
have [B [hB hlarge]] := hex.
pose H := [set i | i \in B].
have hHD : H `<=` D by move=> i hi; exact: hB i hi.
have hHf : finite_set H := finite_fset B.
have hHsum : nonnegative_sum H f = \sum_(i <- B) f i.
  apply: nonnegative_sum_finite=> i hi; exact: hnon i (hB i hi).
have hsub : D `\` H `<=` D by move=> i [].
have hPf : nonnegative_sum H f \is a fin_num.
  rewrite ge0_fin_numE; last exact: nonnegative_sum_nonnegative.
  exact: le_lt_trans (@nonnegative_sum_subset R I H D f hHD) hfinite.
have hTf : nonnegative_sum (D `\` H) f \is a fin_num.
  rewrite ge0_fin_numE; last exact: nonnegative_sum_nonnegative.
  exact: le_lt_trans (@nonnegative_sum_subset R I (D `\` H) D f hsub) hfinite.
pose b := fine (nonnegative_sum H f).
pose t := fine (nonnegative_sum (D `\` H) f).
have hi : D `&` H = H.
  apply/seteqP; split.
  - by move=> i [_ hi].
  - move=> i hi; split=> //; exact: hHD i hi.
have hsplit := @nonnegative_sum_split R I D H f hnon.
rewrite hi in hsplit.
change (S = nonnegative_sum H f + nonnegative_sum (D `\` H) f) in hsplit.
rewrite hSval -(fineK hPf) -(fineK hTf) -EFinD in hsplit.
have hr : M = (b+t)%R := EFin_inj hsplit.
have hb : (M-e < b)%R.
  by move: hlarge; rewrite -hHsum -(fineK hPf) lte_fin.
have hsmall : (t < e)%R.
  by move: hb; rewrite ltrBlDr hr ltrD2l.
exists H; split=> //; split=> //.
by rewrite -(fineK hTf) lte_fin.
Qed.
