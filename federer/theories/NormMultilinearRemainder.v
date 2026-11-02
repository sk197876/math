(** Federer (1969), 3.1.1(4), p. 210: quadratic control of the
    multilinear increment after its first-order terms are removed.
    The proof telescopes twice over the factors and uses only their
    supplied norm laws and the proved product bound. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import RealNormUP TensorFamilyUP FamilyUpdate
  MultilinearFamilyAlgebra FiniteProductFactorBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Remainder.
Variable R : realType.
Variable m : nat.
Variable V : 'I_m -> lmodType R.
Variable Y : lmodType R.
Variable N : forall i, V i -> R.
Arguments N i _ : clear implicits.
Variable NY : Y -> R.
Hypothesis hN : forall i, is_real_norm (N i).
Arguments hN i : clear implicits.
Hypothesis hNY : is_real_norm NY.
Variable f : {dffun forall i, V i} -> Y.
Hypothesis hf : multilinear f.
Variable C : R.
Hypothesis hC : 0 <= C.
Hypothesis hb : forall x, NY (f x) <= C*\prod_(i<m) N i (x i).

(** Source for [norm_multilinear_single_slot_bound]: the linear
    part of the expansion in 3.1.1(4), p. 210, has a finite
    homogeneous bound in its varying coordinate. *)
Lemma norm_multilinear_single_slot_bound (a : {dffun forall i, V i})
    i (v : V i) (B H : R) :
  1 <= B -> 0 <= H -> N i v <= H ->
  (forall k, k != i -> N k (a k) <= B) ->
  NY (f (family_with a v)) <= C*(H*(B^+m)).
Proof.
move=> hB hH hv ha; apply: le_trans (hb _) _.
apply: ler_wpM2l; first exact hC.
apply: (@finite_product_one_small_factor R m
  (fun k => N k (family_with a v k)) i B H hB hH).
- move=> k; exact: real_seminorm_nonnegative (hN k).1 _.
- by rewrite family_with_in.
- move=> k hki; rewrite family_with_out; first exact: ha k hki.
  by rewrite eq_sym.
Qed.

(** Source for [norm_multilinear_slot_error]: the coefficient of
    the ith increment changes by a quantity quadratic in the
    increment norm, supporting the differential in 3.1.1(4), p. 210.
    The second telescoping expansion has a zero diagonal term. *)
Lemma norm_multilinear_slot_error (a h : {dffun forall i, V i})
    (i : 'I_m) (B H : R) :
  1 <= B -> 0 <= H ->
  (forall k, N k (h k) <= H) ->
  (forall k, N k (a k)+N k (h k) <= B) ->
  NY (f (family_with (family_prefix_mix a
      [ffun k : 'I_m => a k+h k] i) (h i))-
      f (family_with a (h i))) <= m%:R*(C*(H*H*(B^+m))).
Proof.
move=> hB hH hh ha.
pose y := [ffun k : 'I_m => a k+h k].
pose s := family_with a (h i).
pose t := family_with (family_prefix_mix a y i) (h i).
have hna k : N k (a k) <= B.
  have hn := real_seminorm_nonnegative (hN k).1 (h k).
  have hak := ha k; lra.
have hsb k : k != i -> N k (s k) <= B.
  move=> hki; rewrite /s family_with_out; first exact: hna.
  by rewrite eq_sym.
have htb k : k != i -> N k (t k) <= B.
  move=> hki; rewrite /t family_with_out; last by rewrite eq_sym.
  rewrite /family_prefix_mix ffunE; case: ifP=> _; last exact: hna.
  rewrite /y ffunE; exact: le_trans (real_seminorm_triangle (hN k).1 _ _) (ha k).
have hterm : forall j : 'I_m,
    NY (f (family_with (family_prefix_mix s t j) (t j-s j))) <= C*(H*H*(B^+m)).
  move=> j; case: (eqVneq i j)=> [<-|hij].
  - rewrite /t /s !family_with_in subrr (multilinear_family_zero hf)
      (real_seminorm_zero hNY.1).
    apply: mulr_ge0=> //; apply: mulr_ge0; first exact: (mulr_ge0 hH hH).
    apply: exprn_ge0; exact: le_trans ler01 hB.
  - pose u := family_with (family_prefix_mix s t j) (t j-s j).
    have hui : N i (u i) <= H.
      rewrite /u family_with_out; last by rewrite eq_sym.
      rewrite /family_prefix_mix ffunE; case: ifP=> _;
        by rewrite /s /t family_with_in; exact: hh.
    have huj : N j (u j) <= H.
      rewrite /u family_with_in /s /t !family_with_out // /family_prefix_mix ffunE.
      case: ifP=> _.
      + by rewrite /y ffunE addrAC subrr add0r; exact: hh.
      + by rewrite subrr (real_seminorm_zero (hN j).1).
    have huk : forall k, k != i -> k != j -> N k (u k) <= B.
      move=> k hki hkj; rewrite /u family_with_out; last by rewrite eq_sym.
      rewrite /family_prefix_mix ffunE; case: ifP=> _.
      + exact: htb k hki.
      + exact: hsb k hki.
    apply: le_trans (hb u) _; apply: ler_wpM2l; first exact hC.
    apply: (@finite_product_two_small_factors R m (fun k => N k (u k))
      i j B H H hij hB hH hH) => // k.
    exact: real_seminorm_nonnegative (hN k).1 _.
change (NY (f t-f s) <= m%:R*(C*(H*H*(B^+m)))).
rewrite (multilinear_family_difference hf).
apply: le_trans (real_seminorm_sum hNY.1 _) _.
have hs : (\sum_(j<m) NY (f (family_with (family_prefix_mix s t j) (t j-s j))))
    <= \sum_(j<m) C*(H*H*(B^+m)).
  by apply: ler_sum=> j _; exact: hterm.
by rewrite sumr_const card_ord -mulr_natl in hs.
Qed.

(** Source for [norm_multilinear_quadratic_remainder]: the
    displayed derivative of Federer 3.1.1(4), p. 210, with an
    explicit quadratic remainder estimate. All factors and the
    target can have arbitrary dimension. *)
Theorem norm_multilinear_quadratic_remainder
    (a h : {dffun forall i, V i}) (B H : R) :
  1 <= B -> 0 <= H ->
  (forall k, N k (h k) <= H) ->
  (forall k, N k (a k)+N k (h k) <= B) ->
  NY (f [ffun k : 'I_m => a k+h k]-f a-
      \sum_(i<m) f (family_with a (h i))) <=
    (m%:R*(m%:R*C*(B^+m)))*(H*H).
Proof.
move=> hB hH hh ha.
have hinc := @multilinear_family_difference R m V Y f hf a
  [ffun k : 'I_m => a k+h k].
have he : f [ffun k : 'I_m => a k+h k]-f a =
    \sum_(i<m) f (family_with (family_prefix_mix a
      [ffun k : 'I_m => a k+h k] i) (h i)).
  rewrite hinc; apply: eq_bigr=> i _.
  by rewrite ffunE addrAC subrr add0r.
rewrite he -sumrB.
apply: le_trans (real_seminorm_sum hNY.1 _) _.
have hs : (\sum_(i<m) NY
    (f (family_with (family_prefix_mix a [ffun k : 'I_m => a k+h k] i) (h i))-
      f (family_with a (h i)))) <= \sum_(i<m) m%:R*(C*(H*H*(B^+m))).
  apply: ler_sum=> i _; exact: norm_multilinear_slot_error hB hH hh ha.
rewrite sumr_const card_ord -(mulr_natl (m%:R*(C*(H*H*(B^+m)))) m) in hs.
have heq : m%:R*(m%:R*(C*(H*H*(B^+m)))) =
    (m%:R*(m%:R*C*(B^+m)))*(H*H) by ring.
by rewrite heq in hs.
Qed.
End Remainder.
