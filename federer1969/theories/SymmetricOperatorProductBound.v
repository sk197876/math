(** Federer (1969), 1.10.5, p. 47, the binary product inequality with
    binomial coefficient. The binary estimate does not require
    associativity. We retain all degrees and allow infinite form norms,
    using nonnegative extended multiplication with zero times infinity zero. *)
From mathcomp Require Import all_boot all_order all_algebra fingroup perm
  classical_sets reals constructive_ereal.
From Federer Require Import TensorUP Bilinear RealNormUP SymmetricForms
  SymmetricFormProduct SymmetricFormShuffle Shuffles AlternatingShuffle
  ShuffleCardinalityBound SymmetricOperatorNormUP SymmetricOperatorNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [extended_constant_finite_sum]: Federer 1.10.5,
    p. 47, supporting count of equal shuffle bounds. A finite
    sum of an extended constant is its product with the cardinality. *)
Lemma extended_constant_finite_sum (R : realType) (I : finType) (c : \bar R) :
  (\sum_(i : I) c = (#|I|)%:R%:E * c)%E.
Proof. by rewrite big_const mule_natl /enatmul Monoid.Theory.iteropE. Qed.

Section Product.
Variable R : realType.
Variables V W : lmodType R.
Variable NV : V -> R.
Variable NW : W -> R.
Hypothesis hV : is_real_seminorm NV.
Hypothesis hW : is_real_seminorm NW.
Variable mu : W -> W -> W.
Hypothesis hmu : bilinear mu.
Hypothesis hsub : forall x y, NW (mu x y) <= NW x * NW y.

(** Source for [symmetric_shuffle_left_unit]: Federer 1.10.5,
    p. 47, supporting shuffle argument: a left block of a
    permuted unit tuple is again a unit tuple for the same norm. *)
Lemma symmetric_shuffle_left_unit p q (t : (p+q).-tuple V) (sigma : 'S_(p+q)) :
  symmetric_form_unit_tuple NV t -> symmetric_form_unit_tuple NV (shuffle_left_tuple t sigma).
Proof.
move=> ht i; have hm := mem_tnth i (shuffle_left_tuple t sigma).
case/mapP: hm=> j hj ->; have hj' := mem_take hj.
case/mapP: hj'=> k hk ->; rewrite -tnth_nth; exact: ht.
Qed.

(** Source for [symmetric_shuffle_right_unit]: Federer 1.10.5,
    p. 47, supporting shuffle argument for the right block,
    including a block of degree zero. *)
Lemma symmetric_shuffle_right_unit p q (t : (p+q).-tuple V) (sigma : 'S_(p+q)) :
  symmetric_form_unit_tuple NV t -> symmetric_form_unit_tuple NV (shuffle_right_tuple t sigma).
Proof.
move=> ht i; have hm := mem_tnth i (shuffle_right_tuple t sigma).
case/mapP: hm=> j hj ->; have hj' := mem_drop hj.
case/mapP: hj'=> k hk ->; rewrite -tnth_nth; exact: ht.
Qed.

(** Source for [symmetric_operator_product_bound]: Federer 1.10.5,
    p. 47, the displayed product norm inequality. The norm of
    the symmetric product of a p-form and a q-form is at most
    binomial(p+q,p) times the product of their norms. Only bilinearity
    and the stated submultiplicative output seminorm are required. *)
Theorem symmetric_operator_product_bound p q (f : S_m V W p) (g : S_m V W q) :
  (symmetric_operator_norm hV NW (sform_product hmu f g) <=
    ('C(p+q,p))%:R%:E *
      (symmetric_operator_norm hV NW f * symmetric_operator_norm hV NW g))%E.
Proof.
pose a := symmetric_operator_norm hV NW f.
pose b := symmetric_operator_norm hV NW g.
have ha : (0 <= a)%E := @symmetric_operator_norm_ge_zero R V W NV hV NW hW p f.
have hb : (0 <= b)%E := @symmetric_operator_norm_ge_zero R V W NV hV NW hW q g.
apply: symmetric_operator_norm_least=> t ht.
rewrite sform_product_shuffle.
have hsum := @real_seminorm_sum R W NW hW (Finite.clone (Sh p q) _)
  (fun s => mu (f (shuffle_left_tuple t (val s))) (g (shuffle_right_tuple t (val s)))).
apply: (le_trans (lee_tofin hsum)); rewrite -sumEFin.
apply: (le_trans (_ : (\sum_(s : Sh p q)
    (NW (mu (f (shuffle_left_tuple t (val s))) (g (shuffle_right_tuple t (val s)))))%:E
  <= \sum_(s : Sh p q) (a*b))%E)).
  apply: lee_sum=> s _; apply: (le_trans (lee_tofin (hsub _ _))); rewrite EFinM.
  apply: lee_pmul.
  - rewrite lee_fin; exact: real_seminorm_nonnegative hW _.
  - rewrite lee_fin; exact: real_seminorm_nonnegative hW _.
  - apply: symmetric_operator_norm_upper; exact: symmetric_shuffle_left_unit ht.
  - apply: symmetric_operator_norm_upper; exact: symmetric_shuffle_right_unit ht.
rewrite extended_constant_finite_sum; apply: lee_wpmul2r; first exact: mule_ge0 ha hb.
rewrite lee_fin ler_nat; exact: shuffle_cardinality_bound.
Qed.
End Product.
