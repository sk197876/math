(** Federer (1969), 2.2.3, p. 62: restriction by a Borel set preserves Borel
    regularity. the proof below uses its cover D union the complement of A
    in the Borel special case. Source context: BorelRegularMeasureUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureRestriction
  BorelFamilyBasic TopologicalBorel BorelRegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [borel_regular_restrict_borel]: Federer 2.2.3, p. 62: if mu
    is Borel regular and A is Borel, then mu restricted to A is Borel
    regular. The separate measure laws are already established in 2.1.2. *)
Theorem borel_regular_restrict_borel (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hm : is_measure mu)
    (hr : is_borel_regular_measure mu) A :
  borel_set A -> is_borel_regular_measure (measure_restrict mu A).
Proof.
move=> hA; constructor.
- move=> U hU; apply: measure_restrict_measurable.
  exact: (@borel_regular_open_measurable R T mu hr U hU).
- move=> X; have [D [hXD [hD he]]] := borel_regular_cover hr (A `&` X).
  exists (D `|` ~` A); split.
  + move=> x hx; case: (pselect (A x))=> ha; last by right.
    left; apply: hXD; by split.
  + split.
    * exact: (@borel_family_binary_union _ setT _ (borel_sets_family T)
        D (~` A) hD (borel_set_complement hA)).
    * apply/eqP; rewrite eq_le; apply/andP; split.
      -- apply: (@measure_mono R _ _ (measure_restrict_is_measure hm A)).
         move=> x hx; case: (pselect (A x))=> ha; last by right.
         left; apply: hXD; by split.
      -- rewrite /measure_restrict he; apply: (@measure_mono R _ mu hm).
         move=> x [ha [hd|hn]] //; exfalso; exact: hn ha.
Qed.
