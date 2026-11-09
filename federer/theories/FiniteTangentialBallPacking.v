(** Federer (1969), 3.3.19, p. 306: finite
    projected-centre packing for the small-ball part of
    the final upper-density assertion. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets topology lra.
From Federer Require Import FiniteStrictSeparatedInterval FiniteStrictSpreadPair.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Packing.
Variable R:realType.
Variable X:metricType R.
Variable f:X->R.
Hypothesis hNonexpanding:forall x y:X,`|f x-f y|<=mdist x y.

(** Source for [finite_tangential_ball_count]: original
    centres within distance t+h of a, whose scalar
    tangent coordinates are strictly more than 6h apart,
    satisfy card(F)6h<2t+8h. Exact finite image cardinality
    and strict interval packing prove the bound supporting
    3.3.19, p. 306. *)
Theorem finite_tangential_ball_count (F:{fset X}) (a:X) (t h:R):
  (2<=#|` F|)%N ->0<h ->0<=t ->
  (forall x,x \in F ->mdist x a<=t+h) ->
  (forall x y,x \in F ->y \in F ->x!=y ->6* h<`|f x-f y|) ->
  #|` F|%:R*(6* h)<2* t+8* h.
Proof.
move=>hCount hh ht hBounds hSeparate.
pose G:=[fset f x|x in F].
have hInjective:{in F &,injective f}.
  move=>x y hx hy hEqual.
  case:(eqVneq x y)=>[hEq|hDifferent];first exact:hEq.
  have hNear:= hSeparate x y hx hy hDifferent.
  rewrite hEqual subrr normr0 in hNear;exfalso;nra.
have hCard:#|` G|=#|` F| by rewrite /G card_in_imfset.
have hGCount:(2<=#|` G|)%N by rewrite hCard.
have hWidth:0<6* h by nra.
have hInterval:f a-(t+h)<=f a+(t+h) by nra.
have hGWithin z:z \in G ->f a-(t+h)<=z /\z<=f a+(t+h).
  move=>/imfsetP[x hx ->].
  have hNorm:= le_trans (hNonexpanding x a) (hBounds x hx).
  have /andP[hL hR]:(-(t+h)<=f x-f a<=t+h) by rewrite -ler_norml.
  split;nra.
have hGSeparated x y:x \in G ->y \in G ->x!=y ->6* h<`|x-y|.
  move=>/imfsetP[u hu ->] /imfsetP[v hv ->] hDifferent.
  have huv:u!=v by apply/eqP=>hEqual;move:hDifferent;rewrite hEqual eqxx.
  exact:hSeparate u v hu hv huv.
have hPacking:= @finite_strict_separated_interval_bound R G (f a-(t+h)) (f a+(t+h)) (6* h)
  hGCount hWidth hInterval hGWithin hGSeparated.
rewrite hCard in hPacking;nra.
Qed.

(** Source for [finite_tangential_ball_extreme_pair]: three
    actual centres with tangent-coordinate spacing >6h have
    two actual members more than 12h apart in the ORIGINAL
    metric. The local extrema are retained as existence
    witnesses, supporting the translated-piece case of
    3.3.19, p. 306. *)
Theorem finite_tangential_ball_extreme_pair (F:{fset X}) (h:R):
  (3<=#|` F|)%N ->0<h ->
  (forall x y,x \in F ->y \in F ->x!=y ->6* h<`|f x-f y|) ->
  exists x y:X,x \in F /\y \in F /\12* h<mdist x y.
Proof.
move=>hCount hh hSeparate.
pose G:=[fset f x|x in F].
have hInjective:{in F &,injective f}.
  move=>x y hx hy hEqual.
  case:(eqVneq x y)=>[hEq|hDifferent];first exact:hEq.
  have hNear:= hSeparate x y hx hy hDifferent.
  rewrite hEqual subrr normr0 in hNear;exfalso;nra.
have hCard:#|` G|=#|` F| by rewrite /G card_in_imfset.
have hGCount:(3<=#|` G|)%N by rewrite hCard.
have hWidth:0<6* h by nra.
have hGSeparated x y:x \in G ->y \in G ->x!=y ->6* h<`|x-y|.
  move=>/imfsetP[u hu ->] /imfsetP[v hv ->] hDifferent.
  have huv:u!=v by apply/eqP=>hEqual;move:hDifferent;rewrite hEqual eqxx.
  exact:hSeparate u v hu hv huv.
have [u [v [hu [hv hSpread]]]]:= @finite_strict_spread_pair R G (6* h) hGCount hWidth hGSeparated.
have /imfsetP[x hx hX]:u \in G:= hu.
have /imfsetP[y hy hY]:v \in G:= hv.
have hNorm:= hNonexpanding y x.
rewrite -hX -hY in hNorm.
have hSpread0:0<=v-u by nra.
rewrite (ger0_norm hSpread0) (metric_sym y x) in hNorm.
exists x,y;split=>//;split=>//;nra.
Qed.
End Packing.
