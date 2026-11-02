(** Federer (1969), 3.1.11, p. 221:
    equality of symmetric forms is determined by
    their diagonal values, using the polarization
    theorem already proved for 1.10.4, p. 46. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom ContinuousMultilinearUP FiniteArgumentPermutation
  MultilinearTupleForm SymmetricForms HomogeneousPolynomialFunctions PolynomialDiagonalNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [continuous_multilinear_symmetric_diagonal_injective]:
    polarization turns the linewise coefficient
    comparison into equality of the full
    higher differentials, Federer 3.1.11,
    p. 221, using 1.10.4, p. 46.
    This includes degree zero and arbitrary
    source and target dimensions. *)
Theorem continuous_multilinear_symmetric_diagonal_injective (R : realType) k
    (X Y Z : lmodType R) (NX : X->R) (NY : Y->R)
    (ev : {ffun 'I_k->X}->Hom Z Y) (ZN : Z->R)
    (hZ : is_continuous_multilinear_space NX NY ev ZN) (z w : Z) :
  (forall s u, ev (finite_argument_permutation s u) z=ev u z) ->
  (forall s u, ev (finite_argument_permutation s u) w=ev u w) ->
  (forall x, ev [ffun _ : 'I_k=>x] z=ev [ffun _ : 'I_k=>x] w) ->
  z=w.
Proof.
move=>hz hw hdiag.
have [phi hphi] := symmetric_multilinear_tuple_form_exists
  (continuous_multilinear_evaluation hZ z) hz.
have [psi hpsi] := symmetric_multilinear_tuple_form_exists
  (continuous_multilinear_evaluation hZ w) hw.
have hp : phi=psi.
  apply: (@sform_polynomial_injective R X Y k (@pchar_num R)).
  apply: funext=>x.
  rewrite !sform_polynomial_diagonal_value hphi hpsi.
  have hu : [ffun i=>tnth [tuple x | j<k] i]=[ffun _ : 'I_k=>x].
    by apply/ffunP=>i; rewrite !ffunE tnth_mktuple.
  by rewrite hu hdiag.
apply: (continuous_multilinear_extensional hZ)=>u.
have hh := congr1 (fun q : S_m X Y k=>q [tuple u i | i<k]) hp.
rewrite hphi hpsi in hh.
have hu : [ffun i=>tnth [tuple u j | j<k] i]=u.
  by apply/ffunP=>i; rewrite !ffunE tnth_mktuple.
by rewrite hu in hh.
Qed.
