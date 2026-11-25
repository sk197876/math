(** Federer (1969), 1.10.5, p. 47: supporting permutation formula for
    products of one-forms. *)
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From Federer Require Import Hom BoundedHom SymmetricAlgebra SymmetricGrading
  SymmetricForms SymmetricFormWords SymmetricFormSum SymmetricFormProduct
  SymmetricFormUnit ScalarCoefficients SymmetricUniformOneForms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [ordinal_cast_enum_map]: Federer 1.10.5, p. 47,
    supporting index transport: mapping a family over equal ordinal
    bounds gives the same ordered list. No mathematical choice is involved. *)
Lemma ordinal_cast_enum_map (T : Type) n m (h : n = m) (f : 'I_m -> T) :
  [seq f (cast_ord h i) | i <- enum 'I_n] = [seq f i | i <- enum 'I_m].
Proof. by case: m / h in f *; apply: eq_map=> i; congr (f _); apply: val_inj. Qed.

Section Formula.
Variable K : fieldType.
Variable V : lmodType K.
Variable m : nat.
Variable omega : 'I_m -> S_m V K^o 1.

(** Source for [symmetric_one_form_product_permutations]: Federer
    1.10.5, p. 47, supporting formula from 1.10.2, p. 45.
    An actual nonempty product of one-forms, evaluated on m vectors,
    equals the sum over permutations of the products of their values. *)
Theorem symmetric_one_form_product_permutations (t : m.-tuple V) :
  (0 < m)%N ->
  (foldr (symmetric_forms_product (scalar_bilinear K))
      (@symmetric_coefficient_form K V K^o 1)
      [seq sform_include (omega i) | i <- enum 'I_m]) (symmetric_word t) =
    \sum_(sigma : 'S_m) \prod_(i < m) sform_words (omega i) [:: tnth t (sigma i)].
Proof.
move=> hm.
have hone : all (pred1 1%N) (nseq m 1%N) by rewrite all_nseq /= eqxx orbT.
have hn : sumn (nseq m 1%N) = m by rewrite sumn_nseq mul1n.
have hd : nseq m 1%N != [::] by rewrite -size_eq0 size_nseq -lt0n.
pose hs := size_nseq m 1%N.
have hf := @uniform_symmetric_one_forms_formula_degree K V
  (nseq m 1%N) hone (fun i => omega (cast_ord hs i)) m hn t hd.
rewrite (ordinal_cast_enum_map hs (fun i => sform_include (omega i))) in hf.
rewrite hf; apply: eq_bigr=> sigma _.
have hb : bijective (@cast_ord (size (nseq m 1%N)) m hs).
  exists (cast_ord (esym hs)); [exact: cast_ordK | exact: cast_ordKV].
rewrite (reindex _ (onW_bij _ hb)).
apply: eq_bigr=> i _; congr (sform_words _ [:: tnth t (sigma _)]).
exact: val_inj.
Qed.
End Formula.
