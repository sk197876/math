(** Federer (1969), 2.5.10, p. 101: agreement of the original functional and
    the glued density pairing on finite unions of pieces. The finite-union
    step uses only linearity and cutoff laws, and does not require the two
    pieces to be disjoint. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureFiniteClosure FunctionLatticeUP FunctionLatticeSeminormUP
  LatticeAdditiveFunctional VectorFunctionLattice TotalScalarLpUP TotalScalarLpLattice TotalScalarLpClosure
  TotalScalarLpCharacteristic CharacteristicFunctionSealed TotalScalarCutoff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [cutoff_functionals_agree]: supporting local equality for the
    disjoint-gluing argument in Federer 2.5.10, p. 101 *)
Definition cutoff_functionals_agree (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (A C : (X -> R) -> R) (U : set X) :=
  forall f, total_scalar_lp mu 1 f -> A (total_scalar_cutoff U f)=C (total_scalar_cutoff U f).

(** Source for [cutoff_functionals_agree_empty]: supporting empty
    union case for Federer 2.5.10, p. 101. *)
Lemma cutoff_functionals_agree_empty (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A C : (X -> R) -> R) :
  is_linear_functional_on_functions (total_scalar_lp mu 1) A ->
  is_linear_functional_on_functions (total_scalar_lp mu 1) C ->
  cutoff_functionals_agree mu A C set0.
Proof.
move=> hA hC f hf.
have he : total_scalar_cutoff set0 f=(fun _ => 0%R).
  apply: funext=> x; exact: total_scalar_cutoff_off.
rewrite he.
have hL := @total_scalar_lp_vector_lattice R X mu hm 1 (lexx _).
by rewrite (@lattice_additive_zero R X _ A hL.1 hA.1 f hf)
  (@lattice_additive_zero R X _ C hL.1 hC.1 f hf).
Qed.

(** Source for [cutoff_functionals_agree_union]: supporting
    finite-union induction for Federer 2.5.10, p. 101.
    The second contribution is cut off on V outside U, so overlapping
    pieces are permitted. *)
Lemma cutoff_functionals_agree_union (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A C : (X -> R) -> R) (U V : set X) :
  is_linear_functional_on_functions (total_scalar_lp mu 1) A ->
  is_linear_functional_on_functions (total_scalar_lp mu 1) C ->
  measure_measurable mu U -> measure_measurable mu V ->
  cutoff_functionals_agree mu A C U -> cutoff_functionals_agree mu A C V ->
  cutoff_functionals_agree mu A C (U `|` V).
Proof.
move=> hA hC hU hV hAU hAV f hf.
have cut (E : set X) (hE : measure_measurable mu E) : total_scalar_lp mu 1 (total_scalar_cutoff E f).
  exact: (@total_scalar_lp_characteristic_piece R X mu hm 1 E _ f (@CharacteristicFunction.laws R X E) hE hf).
have huf := cut U hU.
have hnf := cut (~` U) (measure_measurable_complement hU).
have hvnf := @total_scalar_lp_characteristic_piece R X mu hm 1 V _ (total_scalar_cutoff (~` U) f)
  (@CharacteristicFunction.laws R X V) hV hnf.
have he : total_scalar_cutoff (U `|` V) f=
    (fun x => (total_scalar_cutoff U f x+total_scalar_cutoff V (total_scalar_cutoff (~` U) f) x)%R).
  apply: funext=> x; case: (pselect (U x))=> hu.
  - have hun : ~ (~` U) x by move=> hn; exact: hn hu.
    rewrite (total_scalar_cutoff_on f (or_introl hu)) (total_scalar_cutoff_on f hu).
    case: (pselect (V x))=> hv.
    + by rewrite (total_scalar_cutoff_on (total_scalar_cutoff (~` U) f) hv) (total_scalar_cutoff_off f hun) addr0.
    + by rewrite (total_scalar_cutoff_off (total_scalar_cutoff (~` U) f) hv) addr0.
  - rewrite (total_scalar_cutoff_off f hu) add0r.
    case: (pselect (V x))=> hv.
    + by rewrite (total_scalar_cutoff_on f (or_intror hv)) (total_scalar_cutoff_on (total_scalar_cutoff (~` U) f) hv) (total_scalar_cutoff_on f hu).
    + have hn : ~ (U `|` V) x by move=> [hx|hx]; [exact: hu hx|exact: hv hx].
      by rewrite (total_scalar_cutoff_off f hn) (total_scalar_cutoff_off (total_scalar_cutoff (~` U) f) hv).
rewrite he (hA.1 _ _ huf hvnf) (hC.1 _ _ huf hvnf) (hAU f hf) (hAV _ hnf).
by [].
Qed.
