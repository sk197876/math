(** Federer (1969), 3.2.14, p. 252: maximize
    a finite measure on the countably rectifiable
    Borel class. This supporting order argument proves
    attainment from countable-union closure and monotonicity;
    it introduces no maximality axiom. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealBoundsUP ExtendedRealBounds ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countable_union_family_maximum]: the
    countable maximization supporting the final existence
    assertion of Federer 3.2.14, p. 252. Every
    closure and score-bound premise is explicit and
    must be discharged for the actual Borel class. *)
Theorem countable_union_family_maximum (R : realType) (X : Type)
    (C : set (set X)) (r : set X -> R) (M : R) :
  (exists A, C A) -> (forall A, C A -> (0<=r A<=M)%R) ->
  (forall F : nat -> set X, (forall n, C (F n)) -> C (\bigcup_n F n)) ->
  (forall A B, C A -> C B -> A `<=` B -> (r A<=r B)%R) ->
  exists B, C B /\ forall A, C A -> (r A<=r B)%R.
Proof.
move=> [A0 hA0] hb hU hmono.
pose S := [set t : \bar R | exists A, C A /\ t=(r A)%:E].
pose s := extended_real_sup S.
have hs0 : 0<=s.
  apply: le_trans (_ : (r A0)%:E<=s).
  - rewrite lee_fin; exact: (andP (hb A0 hA0)).1.
  - apply: extended_real_sup_upper; by exists A0.
have hsM : s<=M%:E.
  apply: extended_real_sup_least=> t [A [hA ->]].
  rewrite lee_fin; exact: (andP (hb A hA)).2.
have hsfin : s \is a fin_num.
  rewrite fin_numElt; apply/andP; split.
  - exact: lt_le_trans (ltNyr (0%R : R)) hs0.
  - exact: le_lt_trans hsM (ltry M).
pose a := fine s.
have hsa : s=a%:E by rewrite /a fineK.
have happ (e : R) : (0<e)%R -> exists A, C A /\ (a-e<r A)%R.
  move=> he; apply: contrapT=> hnone.
  have hle : s<=(a-e)%:E.
    apply: extended_real_sup_least=> t [A [hA ->]].
    rewrite lee_fin leNgt; apply/negP=> hlt; apply: hnone; by exists A.
  have hlt : (a-e)%:E<s by rewrite hsa lte_fin ltrBlDr ltrDl.
  by rewrite ltNge hle in hlt.
have hex n : exists A, C A /\ (a-(n.+1%:R)^-1<r A)%R.
  apply: happ; by rewrite invr_gt0 ltr0n.
have [F hF] := choice hex.
pose B := \bigcup_n F n.
have hB : C B := hU F (fun n => (hF n).1).
have hdom n : (r (F n)<=r B)%R.
  apply: hmono (hF n).1 hB _=> x hx; by exists n.
have haB : (a<=r B)%R.
  rewrite leNgt; apply/negP=> hBa.
  have he : (0<a-r B)%R by rewrite subr_gt0.
  have [n hn] := positive_reciprocal_nat_small he.
  have hlu : (a-(n.+1%:R)^-1<r B)%R := lt_le_trans (hF n).2 (hdom n).
  have hdist : (a-r B<(n.+1%:R)^-1)%R.
    by rewrite ltrBlDr addrC -ltrBlDr.
  by have := lt_trans hn hdist; rewrite ltxx.
exists B; split=> // A hA.
have hh : (r A)%:E<=s by apply: extended_real_sup_upper; exists A; split=> //.
rewrite hsa lee_fin in hh; exact: le_trans hh haB.
Qed.
