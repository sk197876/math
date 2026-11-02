(** Federer (1969), 1.6.6, p. 27, basis of complex-valued real forms. These
    supporting coordinate lemmas apply the basis theorem of 1.3.2, pp.
    14-15, and the form/exterior-power correspondence of 1.4.1, p. 17. They
    do not assume the desired mixed-form basis. Source context are recorded
    in ComplexScalarUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlternatingCoordinates CovectorProducts
  ComplexValuedForms ScalarRestriction FiniteBasisCriterion FiniteIndependence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [form_basis_values_ext]: Federer 1.6.6, p. 27,
    complex-valued form basis. Supporting fact: a form with any coefficient
    module is determined by its values on increasing basis tuples. *)
Lemma form_basis_values_ext (K : fieldType) (h2 : (1+1 : K) != 0)
    (V W : lmodType K) n (e : 'I_n -> V) (he : is_basis e) m
    (a b : A_m V W m) :
  (forall l : Lambda n m, a [tuple of map e (val l)] = b [tuple of map e (val l)]) ->
  a = b.
Proof.
move=> h; apply: pairing_ext => x.
apply: (@basis_linear_ext K (Choice.clone (Lambda n m) _)
  (exterior_power V m) (fun l => e_lambda e (val l)) (finite_e_lambda_basis he h2 m)
  W (hom_as_linear (form_to_hom a)) (hom_as_linear (form_to_hom b))) x => l.
change (pairing (e_lambda e (val l)) a = pairing (e_lambda e (val l)) b).
by rewrite !pairing_e_lambda; exact: h.
Qed.

Section ComplexValues.
Variables R C : fieldType.
Variable embed : {rmorphism R -> C}.
Variable U : lmodType R.
Variable m : nat.
Local Notation CF := (complex_valued_form embed U C^o m).

(** Source for [complex_form_evaluate]: Federer 1.6.6, p. 27,
    complex coordinates of real forms. Evaluation at a tuple, as a
    functional on the complex vector space of forms. *)
Definition complex_form_evaluate (t : m.-tuple U) (a : CF) : C^o := a t.

(** Source for [complex_form_evaluate_linear]: Federer 1.6.6,
    p. 27, complex coordinates of real forms. Evaluation is C-linear. *)
Lemma complex_form_evaluate_linear t : linear (complex_form_evaluate t).
Proof. by move=> c a b. Qed.
HB.instance Definition _ t := GRing.isLinear.Build C CF C^o *:%R
  (complex_form_evaluate t) (complex_form_evaluate_linear t).

Hypothesis hR : (1+1 : R) != 0.
Variable n : nat.
Variable e : 'I_n -> U.
Hypothesis he : is_basis e.

(** Source for [complex_form_basis_values_ext]: Federer 1.6.6,
    p. 27, complex basis of real forms. Values on real increasing
    basis tuples determine the complex-valued form. *)
Lemma complex_form_basis_values_ext (a b : CF) :
  (forall l : Lambda n m, a [tuple of map e (val l)] = b [tuple of map e (val l)]) ->
  a = b.
Proof.
move=> h; apply: (can_inj (@complex_valued_realK R C embed U C^o m)).
exact: (@form_basis_values_ext R hR U (restricted_space embed C^o) n e he m
  (complex_valued_as_real a) (complex_valued_as_real b) h).
Qed.

Variable phi : Lambda n m -> CF.
Hypothesis hp : forall l k : Lambda n m,
  phi l [tuple of map e (val k)] = if l == k then 1 else 0.

(** Source for [complex_form_interpolation_values]: Federer
    1.6.6, p. 27, complex basis of real forms. A family biorthogonal
    to the increasing real basis tuples interpolates arbitrary complex
    coordinate values. Supporting finite-sum calculation. *)
Lemma complex_form_interpolation_values (c : Lambda n m -> C) (k : Lambda n m) :
  (\sum_l c l *: phi l) [tuple of map e (val k)] = c k.
Proof.
change (complex_form_evaluate [tuple of map e (val k)] (\sum_l c l *: phi l) = c k).
rewrite linear_sum.
under eq_bigr do rewrite linearZ.
change ((\sum_l c l * phi l [tuple of map e (val k)]) = c k).
under eq_bigr do rewrite hp.
rewrite (bigD1 k) //= eqxx mulr1.
have hz : (\sum_(l | l != k) c l * (if l == k then 1 else 0)) = 0.
  by apply: big1 => l hl; rewrite (negbTE hl) mulr0.
by rewrite hz addr0.
Qed.

(** Source for [complex_form_biorthogonal_basis]: Federer
    1.6.6, p. 27, complex basis of real forms. Supporting criterion:
    a family dual to all increasing real basis tuples is a C-basis
    of the entire complex-valued real form space. *)
Theorem complex_form_biorthogonal_basis : is_basis phi.
Proof.
apply: finite_basis_criterion.
- apply: (@finite_independent_separating C (Finite.clone (Lambda n m) _) CF phi
    (fun k => GRing.Linear.clone C CF C^o *:%R
      (complex_form_evaluate [tuple of map e (val k)]) _)) => k l.
  change (phi l [tuple of map e (val k)] = if k == l then 1 else 0).
  by rewrite hp eq_sym.
- move=> a; exists (fun l : Lambda n m => a [tuple of map e (val l)]).
  apply: complex_form_basis_values_ext => k.
  by rewrite complex_form_interpolation_values.
Qed.
End ComplexValues.
