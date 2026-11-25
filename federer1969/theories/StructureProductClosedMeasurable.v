(** Federer (1969), 3.3.10, p. 296: actual product-measure
    measurability from the original standing closed-set condition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import CountableOpenBaseUP MeasureUP MeasureFiniteClosure
  ProductMeasure ProductBorelRectangles SuslinSetUP SuslinMeasurability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [structure_product_closed_measurable]: the product
    measurability step of Federer 3.3.10, p. 296, through 2.2.1,
    pp. 59–60, and the product rectangles of 2.6.1–2.6.2,
    pp. 114–115. Countable bases and ORIGINAL factor closed-set
    measurability suffice. Borel regularity and finite whole mass
    of either original factor are not added assumptions. *)
Theorem structure_product_closed_measurable (R:realType)
    (X Y:topologicalType) (alpha:set X->\bar R) (beta:set Y->\bar R)
    (hAlpha:is_measure alpha) (hBeta:is_measure beta)
    (U:nat->set X) (V:nat->set Y):
  is_countable_open_base U ->is_countable_open_base V ->
  (forall C,closed C ->measure_measurable alpha C) ->
  (forall C,closed C ->measure_measurable beta C) ->
  forall C,closed C ->measure_measurable (product_measure hAlpha hBeta) C.
Proof.
move=>hU hV hAlphaClosed hBetaClosed.
have hAlphaOpen O:open O ->measure_measurable alpha O.
  move=>hO; have h:=measure_measurable_complement (hAlphaClosed (~` O) (open_closedC hO)).
  by rewrite setCK in h.
have hBetaOpen O:open O ->measure_measurable beta O.
  move=>hO; have h:=measure_measurable_complement (hBetaClosed (~` O) (open_closedC hO)).
  by rewrite setCK in h.
have hProductOpen:=@product_open_sets_measurable R X Y alpha beta hAlpha hBeta U V
  hU hV hAlphaOpen hBetaOpen.
move=>C hC.
have h:=measure_measurable_complement (hProductOpen (~` C) (closed_openC hC)).
by rewrite setCK in h.
Qed.

(** Source for [structure_product_suslin_measurable]: the original
    incidence sets are product measurable in Federer 3.3.10,
    p. 296. The original standing closed-set condition passes to
    the actual product and then the proved Suslin theorem 2.2.12,
    p. 68. No Borel hull replaces an original incidence set. *)
Theorem structure_product_suslin_measurable (R:realType)
    (X Y:topologicalType) (alpha:set X->\bar R) (beta:set Y->\bar R)
    (hAlpha:is_measure alpha) (hBeta:is_measure beta)
    (U:nat->set X) (V:nat->set Y) (S:set (X*Y)):
  is_countable_open_base U ->is_countable_open_base V ->
  (forall C,closed C ->measure_measurable alpha C) ->
  (forall C,closed C ->measure_measurable beta C) ->
  is_suslin_set R S ->measure_measurable (product_measure hAlpha hBeta) S.
Proof.
move=>hU hV hAlphaClosed hBetaClosed hS.
exact:(@suslin_set_measurable R (X*Y)%type (product_measure hAlpha hBeta)
  (product_measure_is_measure hAlpha hBeta) S
  (@structure_product_closed_measurable R X Y alpha beta hAlpha hBeta U V
    hU hV hAlphaClosed hBetaClosed) hS).
Qed.
