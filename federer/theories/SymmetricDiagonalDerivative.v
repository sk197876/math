(** Federer (1969), 3.1.11, pp. 220–221:
    the first differential of a symmetric homogeneous
    polynomial. Symmetry makes the single-slot
    derivative contributions equal. *)
From mathcomp Require Import all_boot all_order all_algebra reals fingroup perm.
From Federer Require Import Hom RealNormUP TensorFamilyUP FamilyUpdate
  FiniteArgumentPermutation ContinuousMultilinearUP NormDifferentialUP
  NormDiagonalMultilinearDifferential.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [constant_arguments_replacement_transposition]:
    moving the distinguished vector in a tuple of
    otherwise identical vectors, supporting the symmetric
    polynomial derivative in Federer 3.1.11, p. 221. *)
Lemma constant_arguments_replacement_transposition (T : Type) k
    (a v : T) (i j : 'I_k) :
  finite_argument_permutation (tperm i j)
    (@family_with k (fun _=>T) [ffun _ : 'I_k=>a] i v)=
  @family_with k (fun _=>T) [ffun _ : 'I_k=>a] j v.
Proof.
apply/ffunP=> l; rewrite /finite_argument_permutation ffunE.
case: (eqVneq l j)=>[->|hlj].
- by rewrite tpermR !family_with_in.
- have hne : i!=tperm i j l.
    rewrite -{1}(tpermR i j) (inj_eq (perm_inj (s:=tperm i j))).
    by rewrite eq_sym.
  have hjl : j!=l by rewrite eq_sym.
  by rewrite !family_with_out ?hne ?hjl // !ffunE.
Qed.

(** Source for [symmetric_constant_arguments_replacement]:
    all single-slot terms in the derivative of
    a symmetric polynomial coincide, supporting
    Federer 3.1.11, p. 221. *)
Lemma symmetric_constant_arguments_replacement (T U : Type) k
    (f : {ffun 'I_k->T}->U) :
  (forall (s : 'S_k) u, f (finite_argument_permutation s u)=f u) ->
  forall a v (i j : 'I_k),
    f (@family_with k (fun _=>T) [ffun _ : 'I_k=>a] i v)=
    f (@family_with k (fun _=>T) [ffun _ : 'I_k=>a] j v).
Proof.
move=> hf a v i j.
have hh := hf (tperm i j)
  (@family_with k (fun _=>T) [ffun _ : 'I_k=>a] i v).
rewrite constant_arguments_replacement_transposition in hh; exact: esym hh.
Qed.

(** Source for [norm_symmetric_diagonal_differential]:
    first derivative of a continuous symmetric
    homogeneous polynomial, used for D^i P=S_i
    in Federer 3.1.11, p. 221.
    A form of positive degree k+1 contributes
    k+1 equal terms, including arbitrary normed targets. *)
Theorem norm_symmetric_diagonal_differential (R : realType) k
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (f : {ffun 'I_k.+1->X}->Y) :
  norm_bounded_multilinear NX NY f ->
  (forall (s : 'S_k.+1) u, f (finite_argument_permutation s u)=f u) ->
  forall a, exists L : Hom X Y,
    has_norm_differential NX NY (fun _=>True)
      (fun x=>f [ffun _ : 'I_k.+1=>x]) a L /\
    forall v, L v=k.+1%:R*:
      f (@family_with k.+1 (fun _=>X) [ffun _ : 'I_k.+1=>a] ord0 v).
Proof.
move=> hf hs a.
have [L [hL hLe]] := norm_diagonal_multilinear_differential hNX hNY hf a.
exists L; split=> // v; rewrite hLe.
have he (i : 'I_k.+1) :
    f (@family_with k.+1 (fun _=>X) [ffun _ : 'I_k.+1=>a] i v)=
    f (@family_with k.+1 (fun _=>X) [ffun _ : 'I_k.+1=>a] ord0 v).
  exact: symmetric_constant_arguments_replacement hs a v i ord0.
under eq_bigr do rewrite he.
by rewrite sumr_const card_ord scaler_nat.
Qed.
