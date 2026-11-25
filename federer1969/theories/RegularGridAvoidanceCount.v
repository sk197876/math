(** Federer (1969), 3.3.19, p. 305: the complement
    of an angular interval loses its actual grid fraction,
    up to one endpoint grid step. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets lra.
From Federer Require Import RegularGridIntervalLower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [regular_grid_avoidance_count]: an original
    n-grid subfamily avoiding every centre angle in [a,b]
    has weighted cardinality at most nq-(b-a)+q. This
    is the complement form of the original proper-arc
    count used in 3.3.19, p. 305. *)
Theorem regular_grid_avoidance_count (R:realType) (q:R) n (F:{fset 'I_n}) (a b:R):
  0<q ->0<=a ->a<=b ->b<=q* n%:R ->
  (forall k:'I_n,a<=q* k%:R ->q* k%:R<=b ->k \notin F) ->
  #|` F|%:R* q<=q* n%:R-(b-a)+q.
Proof.
move=>hq ha hab hb hAvoid.
pose U:{fset 'I_n}:=[fset k | k:'I_n].
pose G:{fset 'I_n}:=(U `\` F)%fset.
have hU k:k \in U.
  apply/imfsetP;by exists k.
have hInside (k:'I_n):a<=q* k%:R ->q* k%:R<=b ->k \in G.
  move=>hLeft hRight;by rewrite /G in_fsetD (hU k) (hAvoid k hLeft hRight).
have hLower:= @regular_grid_interval_lower R q n G a b hq ha hab hb hInside.
have hIntersection:(U `&` F)%fset= F.
  apply/fsetP=>k;by rewrite in_fsetI (hU k) andTb.
have hCard:= cardfsID F U.
rewrite hIntersection -/G in hCard.
have hUCard:#|` U|= n.
  rewrite /U card_imfset //=;by rewrite -cardE card_ord.
rewrite hUCard in hCard.
have hReal:#|` F|%:R+#|` G|%:R=(n%:R:R) by rewrite -natrD hCard.
nra.
Qed.
