(** Federer (1969), 2.1.6(2), p. 59: transport of the initial-segment
    argument along cardinal embeddings. The matrix argument proves vanishing
    on the ordered representative itself; this module extends that
    conclusion to every smaller cardinal, as required by the definition of
    an Ulam number. This includes empty representatives. Source context:
    UlamSuccessorMatrix.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets functions cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic UlamCardinalUP
  CardinalInjection CardinalSuccessorUP UlamSuccessorMatrix.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.
Local Open Scope ereal_scope.

(** Source for [ulam_set_small_prefixes]: Federer 2.1.6(2),
    p. 59, supporting abstract initial-segment criterion. A comparable
    representative is Ulam if all its strict predecessor sets have
    cardinality bounded by one Ulam set. Injections transfer the
    relation and its predecessor bounds to every smaller measured set. *)
Theorem ulam_set_small_prefixes (R : realType) (I J : choiceType)
    (A : set I) (D : set J) (r : rel J) :
  is_ulam_set R A ->
  (forall x y, D x -> D y -> r x y || r y x) ->
  (forall x, D x -> well_order_prefix D r x #<= A) -> is_ulam_set R D.
Proof.
move=> hu ht hp K mu X hm hX hf ha hz.
case: (pselect (exists d, D d))=> [[d hd]|hempty]; last first.
  have he : D = set0.
    apply/seteqP; split=> [x hx|x []]; exfalso; apply: hempty; by exists x.
  have hx0 : X = set0.
    have hc := hX; rewrite he in hc; exact: (elimT (@card_le0P K J X) hc).
  by rewrite hx0 (measure_empty hm).
have [g [hfun hinj]] := cardinal_injection_with_default d hX.
pose s x y := r (g x) (g y).
have hAeq : Some @` A #= A := card_some.
have hAS : A #<= Some @` A := (proj1 (@card_eqPle _ _ (Some @` A) A) hAeq).2.
have huS : is_ulam_set R (Some @` A).
  exact: (proj2 (@ulam_set_cardinal_invariant R _ _ (Some @` A) A hAeq) hu).
apply: (@ulam_small_prefix_measure_zero R K _ mu hm X (Some @` A) None s huS)=> //.
- move=> x y hx hy; exact: ht (g x) (g y) (hfun x hx) (hfun y hy).
- move=> x hx; apply: card_le_trans _ hAS.
  apply: card_le_trans _ (hp (g x) (hfun x hx)).
  apply: (@cardinal_bound_of_injection K J (well_order_prefix X s x)
    (well_order_prefix D r (g x)) g).
  + move=> y [hy [hyx hne]]; split; first exact: hfun y hy.
    split=> //; move=> he; apply: hne; apply: hinj he; exact: mem_set.
  + move=> y z hy hz' he; apply: hinj he.
    * exact: mem_set (set_mem hy).1.
    * exact: mem_set (set_mem hz').1.
Qed.
