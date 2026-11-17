(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(10), p. 332:
    inject the original fibre into the
    roots of its monic polynomial. Apply
    the existing polynomial root bound and
    cardinal comparison by injection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions cardinality reals.
From Federer Require Import CardinalInjection MonicFiniteFieldRootSet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.

(** Source for [field_finite_fibre_from_monic_root_injection]:
    the original fibre numbers are among
    0,...,k, 3.4.8(10), p. 332.
    The first coordinate is injective only
    on the fibre. Every finite enumeration
    has the actual degree bound. *)
Theorem field_finite_fibre_from_monic_root_injection (R:fieldType) (X:choiceType)
    (F:set X) k (b:'I_k.+1->R) (xi:X->R):
  b ord_max = 1 ->
  (forall x,F x ->\sum_(i<k.+1) b i*(xi x)^+(i:nat)=0) ->
  (forall x y,F x ->F y ->xi x=xi y ->x=y) ->
  finite_set F /\forall s:seq X,uniq s ->(forall x,x \in s ->F x) ->(size s<=k)%N.
Proof.
move=>hLeading hRoots hInjective.
have [hFinite hCount]:=@monic_finite_field_root_set R k b hLeading.
pose Q:set R:=fun t=>\sum_(i<k.+1) b i*t^+(i:nat)=0.
split.
- have hCard:F #<= Q.
    have hMap:set_fun F Q xi by move=>x hx;exact:hRoots x hx.
    have hInj:set_inj F xi.
      move=>x y /asboolP hx /asboolP hy hEqual;exact:hInjective x y hx hy hEqual.
    exact (@cardinal_bound_of_injection X [the choiceType of (R:Type)] F Q xi hMap hInj).
  exact:card_le_finite hCard hFinite.
- move=>s hUniq hF.
  have hMapUniq:uniq (map xi s).
    have hInjOn:{in s &, injective xi}.
      move=>x y hx hy hEqual;exact:hInjective x y (hF x hx) (hF y hy) hEqual.
    by rewrite (map_inj_in_uniq hInjOn).
  have hMapRoots t (ht:t \in map xi s): \sum_(i<k.+1) b i*t^+(i:nat) = 0.
    have [x hx hEqual]:=mapP ht;rewrite hEqual;exact:hRoots x (hF x hx).
  have h:=hCount (map xi s) hMapUniq hMapRoots.
  by rewrite size_map in h.
Qed.
