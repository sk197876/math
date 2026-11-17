(** Supporting Federer (1969), 3.4.8(5), p. 328:
    compare a finite independent family with a finite linear cover.
    This connects the existing Chapter 1 dimension bounds to the
    original finite Taylor coefficient spaces; the target is arbitrary. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import FreeVector LinearBasis FiniteDimension FiniteCoordinates
  FiniteIndependence FiniteBasisComparison FiniteBasisCriterion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [finite_function_coordinate_basis]: standard coordinate
    vectors supporting original finite Taylor coefficients in Federer
    3.4.8(5), p. 328, and the basis convention of 1.1.4, p. 11. *)
Definition finite_function_coordinate_basis (K:fieldType) (I:finType) (i:I):
    {ffun I->K^o}:=[ffun j=>if j==i then 1 else 0].

(** Source for [finite_function_coordinate_basisP]: supporting
    original coefficient dimension count for Federer 3.4.8(5), p. 328.
    The existing finite free-coordinate isomorphism transports the
    original Chapter 1 free basis to the finite function space. *)
Lemma finite_function_coordinate_basisP (K:fieldType) (I:finType):
  is_basis (@finite_function_coordinate_basis K I).
Proof.
have h:=@basis_transport K (Choice.clone I _)
  (GRing.Lmodule.clone K (free_vector K (Choice.clone I _)) _)
  [the lmodType K of {ffun I->K^o}] (@delta K (Choice.clone I _))
  (GRing.Linear.clone _ _ _ _ (@finite_coefficients K I) _)
  (GRing.Linear.clone _ _ _ _ (@finite_coefficients_inverse K I) _)
  (@finite_coefficientsK K I) (@finite_coefficients_inverseK K I)
  (free_basis K (Choice.clone I _)).
apply:(basis_congr _ h)=>i.
by apply/ffunP=>j;rewrite /finite_function_coordinate_basis /finite_coefficients !ffunE deltaE.
Qed.

(** Source for [linear_injection_finite_cover_bound]: supporting
    original finite quotient dimension comparison for Federer
    3.4.8(5), p. 328. Lift the injected original basis through the
    finite cover and apply the existing independent dimension bound.
    No finite-dimensional structure on the covered target is assumed. *)
Theorem linear_injection_finite_cover_bound (K:fieldType) (U W V:lmodType K)
    n (e:'I_n->U) (hE:is_basis e) m (b:'I_m->W) (hB:is_basis b)
    (f:{linear U->V}) (g:{linear W->V}):
  injective f ->(forall v:V,exists w:W,g w = v) ->(n<=m)%N.
Proof.
move=>hInjective hOnto.
have hLifts i:exists w:W,g w = f (e i):=hOnto (f (e i)).
have [w hW]:=choice hLifts.
have hIndependent:finite_independent w.
  move=>c hZero;apply:(finite_basis_independent hE).
  have hh:=congr1 g hZero;rewrite linear_sum linear0 in hh.
  have hMapped:(\sum_i c i*:f (e i)) = 0.
    have hEqual:(\sum_i c i*:f (e i)) = \sum_i g (c i*:w i).
      apply:eq_bigr=>i _;by rewrite linearZ hW.
    by rewrite hEqual.
  apply:hInjective;rewrite linear_sum linear0.
  under eq_bigr do rewrite linearZ.
  exact:hMapped.
have hBound:=@finite_independent_dimension K (finite_basis_vect hB) n w hIndependent.
by rewrite finite_basis_dimension card_ord in hBound.
Qed.

(** Source for [finite_function_injection_cover_card]: supporting
    actual finite-jet counts for Federer 3.4.8(5), p. 328.
    Injecting K^I into a quotient covered by K^J gives |I|<=|J|,
    including empty index sets, by the existing finite basis reindexing. *)
Theorem finite_function_injection_cover_card (K:fieldType) (I J:finType)
    (V:lmodType K) (f:{linear {ffun I->K^o}->V})
    (g:{linear {ffun J->K^o}->V}):
  injective f ->(forall v:V,exists w:{ffun J->K^o},g w = v) ->(#|I|<=#|J|)%N.
Proof.
have hI:=@basis_reindex K (Choice.clone I _) (Choice.clone 'I_(#|I|) _)
  _ (@finite_function_coordinate_basis K I) (@finite_function_coordinate_basisP K I)
  enum_rank enum_val (@enum_rankK I) (@enum_valK I).
have hJ:=@basis_reindex K (Choice.clone J _) (Choice.clone 'I_(#|J|) _)
  _ (@finite_function_coordinate_basis K J) (@finite_function_coordinate_basisP K J)
  enum_rank enum_val (@enum_rankK J) (@enum_valK J).
exact:(linear_injection_finite_cover_bound hI hJ).
Qed.
