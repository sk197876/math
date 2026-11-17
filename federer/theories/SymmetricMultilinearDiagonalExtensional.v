(** Federer (1969), 3.4.8(5), p. 328:
    equality on repeated directions determines the entire
    symmetric derivative action. This is the polarization
    theorem of 1.10.4, p. 46, in the finite-family
    interface of 3.1.11, p. 219. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import TensorFamilyUP FiniteArgumentPermutation MultilinearTupleForm
  SymmetricForms HomogeneousPolynomialFunctions PolynomialDiagonalNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_multilinear_diagonal_extensional]:
    actual symmetric multilinear maps agree on all tuples
    when their repeated-direction values agree, supporting
    3.4.8(5), p. 328, by 1.10.4, p. 46. *)
Theorem symmetric_multilinear_diagonal_extensional (R:realType) k
    (X Y:lmodType R) (f g:{ffun 'I_k->X}->Y):
  multilinear f ->multilinear g ->
  (forall s u,f (finite_argument_permutation s u)=f u) ->
  (forall s u,g (finite_argument_permutation s u)=g u) ->
  (forall x,f [ffun _:'I_k=>x]=g [ffun _:'I_k=>x]) ->forall u,f u=g u.
Proof.
move=>hf hg hs ht hDiagonal.
have [phi hPhi]:=symmetric_multilinear_tuple_form_exists hf hs.
have [psi hPsi]:=symmetric_multilinear_tuple_form_exists hg ht.
have hForms:phi=psi.
  apply:(@sform_polynomial_injective R X Y k (@pchar_num R));apply:funext=>x.
  rewrite !sform_polynomial_diagonal_value hPhi hPsi.
  have hArguments:[ffun i=>tnth [tuple x | j<k] i]=[ffun _:'I_k=>x].
    by apply/ffunP=>i;rewrite !ffunE tnth_mktuple.
  by rewrite hArguments hDiagonal.
move=>u;have hEqual:=congr1 (fun q:S_m X Y k=>q [tuple u i | i<k]) hForms.
rewrite hPhi hPsi in hEqual.
have hArguments:[ffun i=>tnth [tuple u j | j<k] i]=u.
  by apply/ffunP=>i;rewrite !ffunE tnth_mktuple.
by rewrite hArguments in hEqual.
Qed.
