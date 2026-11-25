(** Federer (1969), 2.5.7, p. 99: obtain k+ by maximizing the bounded
    increasing scalar functional r on U. This supporting existence theorem
    isolates the order argument; the hypotheses must separately be proved
    for the actual density family. It introduces no maximality axiom or
    external order-completeness module. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP ExtendedRealBoundsUP ExtendedRealBounds ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [increasing_function_family_maximizer]: supporting countable
    maximization argument of Federer 2.5.7, p. 99 The family is nonempty,
    closed under pointwise maxima, and every increasing sequence has a
    member whose scalar value dominates the sequence. These are explicit
    hypotheses, not claims about an arbitrary function family. *)
Theorem increasing_function_family_maximizer (R : realType) (X : Type)
    (U : set (X -> R)) (r : (X -> R) -> R) (M : R) :
  (exists f, U f) ->
  (forall f, U f -> (0 <= r f <= M)%R) ->
  (forall f g, U f -> U g -> U (fun x => Order.max (f x) (g x))) ->
  (forall f g, U f -> U g -> function_le f g -> (r f <= r g)%R) ->
  (forall v : nat -> X -> R, (forall n, U (v n)) ->
    (forall n x, (v n x <= v n.+1 x)%R) ->
    exists k, U k /\ forall n, (r (v n) <= r k)%R) ->
  exists k, U k /\ (forall f, U f -> (r f <= r k)%R) /\
    extended_real_sup [set t | exists f, U f /\ t=(r f)%:E]=(r k)%:E.
Proof.
move=> [u0 hu0] hb hmax hmono hchain.
pose S := [set t : \bar R | exists f, U f /\ t=(r f)%:E].
pose s := extended_real_sup S.
have hs0 : 0 <= s.
  apply: le_trans (_ : (r u0)%:E <= s).
  - rewrite lee_fin; exact: (andP (hb u0 hu0)).1.
  - apply: extended_real_sup_upper; by exists u0.
have hsM : s <= M%:E.
  apply: extended_real_sup_least=> t [f [hf ->]].
  rewrite lee_fin; exact: (andP (hb f hf)).2.
have hsfin : s \is a fin_num.
  rewrite fin_numElt; apply/andP; split.
  - exact: lt_le_trans (ltNyr (0%R : R)) hs0.
  - exact: le_lt_trans hsM (ltry M).
pose a := fine s.
have hsa : s=a%:E by rewrite /a fineK.
have happ (e : R) : (0 < e)%R -> exists f, U f /\ (a-e < r f)%R.
  move=> he; apply: contrapT=> hnone.
  have hle : s <= (a-e)%:E.
    apply: extended_real_sup_least=> t [f [hf ->]].
    rewrite lee_fin leNgt; apply/negP=> hlt; apply: hnone; by exists f.
  have hlt : (a-e)%:E < s by rewrite hsa lte_fin ltrBlDr ltrDl.
  by move: hlt; rewrite ltNge hle.
have hap n : exists f, U f /\ (a-(n.+1%:R)^-1 < r f)%R.
  apply: happ; by rewrite invr_gt0 ltr0n.
pose u n := projT1 (cid (hap n)).
have hu n := projT2 (cid (hap n)).
pose v := fix v (n : nat) : X -> R :=
  match n with 0%N => u 0%N | m.+1 => fun x => Order.max (v m x) (u m.+1 x) end.
have hv n : U (v n).
  elim: n=> [|n IH]; first exact: (hu 0%N).1.
  exact: hmax _ _ IH (hu n.+1).1.
have hvi n x : (v n x <= v n.+1 x)%R by rewrite /= le_max lexx.
have huv n : function_le (u n) (v n).
  case: n=> [|n] x; first exact: lexx.
  by rewrite /= le_max lexx orbT.
have [k [hk hkv]] := hchain v hv hvi.
have hak : (a <= r k)%R.
  rewrite leNgt; apply/negP=> hka.
  have he : (0 < a-r k)%R by rewrite subr_gt0.
  have [n hn] := @positive_reciprocal_nat_small R (a-r k)%R he.
  have hlu : (a-(n.+1%:R)^-1 < r k)%R.
    exact: lt_le_trans (hu n).2 (le_trans (hmono _ _ (hu n).1 (hv n) (huv n)) (hkv n)).
  have hdist : (a-r k < (n.+1%:R)^-1)%R.
    by rewrite ltrBlDr addrC -ltrBlDr.
  have hbad := lt_trans hn hdist; by rewrite ltxx in hbad.
have hka : (r k <= a)%R.
  have hh : (r k)%:E <= s by apply: extended_real_sup_upper; exists k; split=> //.
  by rewrite hsa lee_fin in hh.
have he : a=r k by apply/eqP; rewrite eq_le hak hka.
exists k; split; first exact: hk.
split.
- move=> f hf.
  have hh : (r f)%:E <= s by apply: extended_real_sup_upper; exists f; split=> //.
  by rewrite hsa he lee_fin in hh.
- by rewrite -he -hsa.
Qed.
