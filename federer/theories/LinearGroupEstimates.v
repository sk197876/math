(** Federer (1969), 2.7.16, p. 134: "If dim V < oo ... we can choose an
    inner product on V and norm Hom(V, V) as in 1.7.6. Then we see that
    composition of linear maps is a continuous operation because f o g - h o
    k = (f - h) o g + h o (g - k), ||f o g|| <= ||f|| . ||g|| whenever f, g,
    h, k in Hom(V, V). Moreover the automorphisms form a dense open subset
    of Hom(V, V), called the linear group of V, and inversion is a
    continuous operation because f^{-1} - g^{-1} = f^{-1} o (g - f) o
    g^{-1}, hence ||f^{-1}|| . (1 - ||g - f|| . ||g^{-1}||) <= ||g^{-1}||,
    whenever f, g are linear automorphisms of V." This module proves the
    displayed identities and estimates for the operator norm of 1.7.6, p.
    33, the resulting bounds ||f o g - h o k|| <= ||f - h|| ||g|| + ||h||
    ||g - k|| and ||f^{-1} - g^{-1}|| <= ||f^{-1}|| ||g - f|| ||g^{-1}||,
    which express the continuity of composition and inversion, the openness
    of the linear group: f is an automorphism whenever ||g - f|| ||g^{-1}||
    < 1, and its density: by the factorisation f = h o g of 1.7.3, p. 30,
    with h orthogonal and g(e_i) = |f(e_i)| e_i, the maps h o (g + t 1_V), t
    > 0, are automorphisms with ||h o (g + t 1_V) - f|| <= t. The
    equivalence of all norms on A(V, V) and the transfer of these properties
    to the affine group are not formalised. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP InnerProductLaws InnerNorm InnerNormInequalities LinearBasis
  OperatorNormUP OperatorNormLaws OperatorNorm TensorUP Bilinear OrthonormalFamilies OrthogonalMaps
  FiniteBasisComparison OrthogonalImageBasis PolarFactorisationUP PolarInjection InnerFiniteSynthesis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Difference.
Variable R : fieldType.
Variable V : lmodType R.

(** Source for [linear_difference]: the map g - f of Hom(V, V),
    Federer 2.7.16, p. 134. Definition of the function. *)
Definition linear_difference (f g : {linear V -> V}) (x : V) : V := f x - g x.

(** Source for [linear_difference_linear]: g - f is linear, Federer
    2.7.16, p. 134. Supporting lemma. *)
Lemma linear_difference_linear (f g : {linear V -> V}) : linear (linear_difference f g).
Proof.
move=> a x y; rewrite /linear_difference (linearP f) (linearP g) scalerBr opprD addrACA.
by [].
Qed.
HB.instance Definition _ (f g : {linear V -> V}) := GRing.isLinear.Build R V V *:%R
  (linear_difference f g) (linear_difference_linear f g).

(** Source for [linear_difference_map]: g - f in Hom(V, V), packaged
    with its linearity, Federer 2.7.16, p. 134. Definition. *)
Definition linear_difference_map (f g : {linear V -> V}) : {linear V -> V} :=
  GRing.Linear.clone _ _ _ _ (linear_difference f g) _.

(** Source for [linear_composition_difference]: Federer 2.7.16, p. 134,
    f o g - h o k = (f - h) o g + h o (g - k). Direct formalisation. *)
Theorem linear_composition_difference (f g h k : {linear V -> V}) (x : V) :
  f (g x) - h (k x) = linear_difference_map f h (g x) + h (linear_difference_map g k x).
Proof. by rewrite /= /linear_difference linearB addrA subrK. Qed.

(** Source for [linear_inverse_difference]: Federer 2.7.16, p. 134,
    f^{-1} - g^{-1} = f^{-1} o (g - f) o g^{-1}, for linear
    automorphisms f, g with inverses f', g'. Direct formalisation. *)
Theorem linear_inverse_difference (f g f' g' : {linear V -> V}) :
  cancel f f' -> cancel g' g -> forall x, f' x - g' x = f' (linear_difference_map g f (g' x)).
Proof.
move=> hff' hg'g x; rewrite /= /linear_difference linearB hff' hg'g.
by [].
Qed.

End Difference.

Section Estimates.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Local Notation N := (inner_norm hB).
Local Notation onorm f := (linear_operator_norm hB hB hb f).

(** Source for [operator_norm_least]: supporting lemma for Federer
    2.7.16, p. 134: if |f(x)| <= M |x| for every x and M >= 0, then
    ||f|| <= M, by 1.7.6, p. 33. *)
Lemma operator_norm_least (f : {linear V -> V}) (M : R) :
  0 <= M -> (forall x, N (f x) <= M * N x) -> onorm f <= M.
Proof.
move=> hM h; apply/(operator_norm_le_unit (linear_operator_normP hB hB hb f))=> x hx.
by apply: le_trans (h x) _; rewrite -[X in _ <= X]mulr1 ler_wpM2l.
Qed.

(** Source for [operator_norm_composition]: Federer 2.7.16, p. 134,
    "||f o g|| <= ||f|| . ||g||". Direct formalisation. *)
Theorem operator_norm_composition (f g : {linear V -> V}) :
  onorm (linear_comp f g) <= onorm f * onorm g.
Proof.
apply: operator_norm_least; first by rewrite mulr_ge0 ?linear_operator_norm_nonnegative.
move=> x; rewrite /linear_comp /=.
apply: le_trans (linear_operator_norm_bound hB hB hb f (g x)) _.
rewrite -mulrA ler_wpM2l ?linear_operator_norm_nonnegative //.
exact: linear_operator_norm_bound.
Qed.

(** Source for [operator_norm_composition_estimate]: Federer 2.7.16,
    p. 134, "composition of linear maps is a continuous operation
    because f o g - h o k = (f - h) o g + h o (g - k),
    ||f o g|| <= ||f|| . ||g||": ||f o g - h o k|| <= ||f - h|| ||g||
    + ||h|| ||g - k||. Direct formalisation. *)
Theorem operator_norm_composition_estimate (f g h k : {linear V -> V}) :
  onorm (linear_difference_map (linear_comp f g) (linear_comp h k)) <=
    onorm (linear_difference_map f h) * onorm g + onorm h * onorm (linear_difference_map g k).
Proof.
apply: operator_norm_least.
  by rewrite addr_ge0 ?mulr_ge0 ?linear_operator_norm_nonnegative.
move=> x.
have he : linear_difference_map (linear_comp f g) (linear_comp h k) x =
    linear_difference_map f h (g x) + h (linear_difference_map g k x).
  by rewrite -linear_composition_difference.
rewrite he; apply: le_trans (inner_norm_triangle hB _ _) _.
rewrite mulrDl; apply: lerD.
- apply: le_trans (linear_operator_norm_bound hB hB hb _ (g x)) _.
  rewrite -mulrA ler_wpM2l ?linear_operator_norm_nonnegative //.
  exact: linear_operator_norm_bound.
- apply: le_trans (linear_operator_norm_bound hB hB hb h _) _.
  rewrite -mulrA ler_wpM2l ?linear_operator_norm_nonnegative //.
  exact: linear_operator_norm_bound.
Qed.

(** Source for [operator_norm_inverse_difference]: Federer 2.7.16,
    p. 134, "f^{-1} - g^{-1} = f^{-1} o (g - f) o g^{-1}", whence
    ||f^{-1} - g^{-1}|| <= ||f^{-1}|| ||g - f|| ||g^{-1}||; this bound
    expresses the continuity of inversion. Direct formalisation. *)
Theorem operator_norm_inverse_difference (f g f' g' : {linear V -> V}) :
  cancel f f' -> cancel g' g ->
  onorm (linear_difference_map f' g') <= onorm f' * onorm (linear_difference_map g f) * onorm g'.
Proof.
move=> hff' hg'g; apply: operator_norm_least.
  by rewrite !mulr_ge0 ?linear_operator_norm_nonnegative.
move=> x.
have he : linear_difference_map f' g' x = f' (linear_difference_map g f (g' x)).
  by rewrite -(linear_inverse_difference hff' hg'g x).
rewrite he.
apply: le_trans (linear_operator_norm_bound hB hB hb f' _) _.
rewrite -!mulrA ler_wpM2l ?linear_operator_norm_nonnegative //.
apply: le_trans (linear_operator_norm_bound hB hB hb _ _) _.
rewrite ler_wpM2l ?linear_operator_norm_nonnegative //.
exact: linear_operator_norm_bound.
Qed.

(** Source for [operator_norm_inverse_estimate]: Federer 2.7.16,
    p. 134, "hence ||f^{-1}|| . (1 - ||g - f|| . ||g^{-1}||) <=
    ||g^{-1}||, whenever f, g are linear automorphisms of V". Direct
    formalisation. *)
Theorem operator_norm_inverse_estimate (f g f' g' : {linear V -> V}) :
  cancel f f' -> cancel g' g ->
  onorm f' * (1 - onorm (linear_difference_map g f) * onorm g') <= onorm g'.
Proof.
move=> hff' hg'g.
have hf' : onorm f' <= onorm g' + onorm f' * onorm (linear_difference_map g f) * onorm g'.
  apply: operator_norm_least.
    by rewrite addr_ge0 ?mulr_ge0 ?linear_operator_norm_nonnegative.
  move=> x.
  have he : f' x = g' x + (f' x - g' x) by rewrite addrC subrK.
  rewrite he.
  have he' : f' x - g' x = f' (linear_difference_map g f (g' x)) := linear_inverse_difference hff' hg'g x.
  rewrite he'.
  apply: le_trans (inner_norm_triangle hB _ _) _; rewrite mulrDl; apply: lerD.
  - exact: linear_operator_norm_bound.
  - apply: le_trans (linear_operator_norm_bound hB hB hb f' _) _.
    rewrite -!mulrA ler_wpM2l ?linear_operator_norm_nonnegative //.
    apply: le_trans (linear_operator_norm_bound hB hB hb _ _) _.
    rewrite ler_wpM2l ?linear_operator_norm_nonnegative //.
    exact: linear_operator_norm_bound.
by rewrite mulrBr mulr1 mulrA lerBlDr.
Qed.

(** Source for [linear_group_open]: "the automorphisms form a ... open
    subset of Hom(V, V)", Federer 2.7.16, p. 134: if g is an
    automorphism with inverse g' and ||g - f|| ||g^{-1}|| < 1, then f is
    univalent, hence an automorphism of the finite dimensional V.
    Direct formalisation of the openness. *)
Theorem linear_group_open (f g g' : {linear V -> V}) :
  cancel g g' -> onorm (linear_difference_map g f) * onorm g' < 1 -> injective f.
Proof.
move=> hgg' hlt x y hxy.
pose z := x - y.
have hz : f z = 0 by rewrite /z linearB hxy subrr.
have hgz : linear_difference_map g f z = g z by rewrite /= /linear_difference hz subr0.
have hb1 : N (g z) <= onorm (linear_difference_map g f) * onorm g' * N (g z).
  have h1 : N (g z) = N (linear_difference_map g f z) by rewrite hgz.
  rewrite {1}h1 -mulrA.
  apply: le_trans (linear_operator_norm_bound hB hB hb _ z) _.
  rewrite ler_wpM2l ?linear_operator_norm_nonnegative //.
  by have := linear_operator_norm_bound hB hB hb g' (g z); rewrite hgg'.
have h0 : N (g z) = 0.
  apply/eqP; rewrite eq_le inner_norm_nonnegative andbT.
  have hp := inner_norm_nonnegative hB (g z).
  have hq := mulr_ge0 (linear_operator_norm_nonnegative hB hB hb (linear_difference_map g f))
    (linear_operator_norm_nonnegative hB hB hb g').
  apply: contraTT hb1; rewrite -ltNge=> hpos; rewrite -ltNge -subr_gt0.
  by rewrite -{1}(mul1r (N (g z))) -mulrBl pmulr_rgt0 // subr_gt0.
have hgz0 : g z = 0 by apply/eqP; rewrite -(inner_norm_eq0 hB) h0.
have : z = 0 by rewrite -(hgg' z) hgz0 linear0.
by move/eqP; rewrite subr_eq0=> /eqP.
Qed.

(** Source for [linear_shift]: the map g + t 1_V, supporting the
    density of the linear group in Federer 2.7.16, p. 134. Definition
    of the function. *)
Definition linear_shift (g : {linear V -> V}) (t : R) (x : V) : V := g x + t *: x.

(** Source for [linear_shift_linear]: g + t 1_V is linear, supporting
    Federer 2.7.16, p. 134. *)
Lemma linear_shift_linear (g : {linear V -> V}) (t : R) : linear (linear_shift g t).
Proof.
move=> a x y; rewrite /linear_shift (linearP g) !scalerDr !scalerA [t * a]mulrC.
by rewrite addrACA.
Qed.
HB.instance Definition _ (g : {linear V -> V}) (t : R) := GRing.isLinear.Build R V V *:%R
  (linear_shift g t) (linear_shift_linear g t).

(** Source for [linear_shift_map]: g + t 1_V packaged with its
    linearity, supporting Federer 2.7.16, p. 134. Definition. *)
Definition linear_shift_map (g : {linear V -> V}) (t : R) : {linear V -> V} :=
  GRing.Linear.clone _ _ _ _ (linear_shift g t) _.

(** Source for [linear_group_dense]: "the automorphisms form a dense ...
    subset of Hom(V, V)", Federer 2.7.16, p. 134: for every linear
    endomorphism f and epsilon > 0 there is a univalent linear map f'
    with ||f' - f|| < epsilon. Direct formalisation, by the orthogonal
    factorisation of 1.7.3, p. 30. *)
Theorem linear_group_dense (f : {linear V -> V}) (eps : R) : 0 < eps ->
  exists f' : {linear V -> V}, injective f' /\ onorm (linear_difference_map f' f) < eps.
Proof.
move=> he.
have [e [heb [ho horth]]] := orthonormal_orthogonal_image_basis hB hB f hb.
have [g [h [[_ hh hhg] [hge _]]]] := polar_injection_prescribed_basis hB hB heb ho
  (finite_basis_independent heb) horth.
pose t := eps / 2.
have ht : 0 < t by rewrite divr_gt0 ?ltr0n.
exists (linear_comp h (linear_shift_map g t)); split.
- move=> x y hxy.
  have hhi := orthogonal_map_injective hB hB hh.
  have hs : linear_shift g t x = linear_shift g t y by apply: hhi; exact: hxy.
  pose z := x - y.
  have hz : linear_shift g t z = 0.
    by rewrite /z (linearB (linear_shift_map g t)) /= hs subrr.
  have hexp : z = \sum_i B z (e i) *: e i.
    have hsyn := @inner_finite_synthesis_coordinates R V B hB n e heb ho z.
    rewrite /inner_finite_synthesis in hsyn; rewrite -[LHS]hsyn; apply: eq_bigr=> i _.
    by rewrite inner_coordinateE.
  have hc j : B z (e j) = 0.
    have h0 : B (linear_shift g t z) (e j) = 0 by rewrite hz (bil0l (inner_bilinear hB)).
    have hsh : linear_shift g t z = \sum_i (B z (e i) * (inner_norm hB (f (e i)) + t)) *: e i.
      rewrite {1}hexp /linear_shift linear_sum scaler_sumr -big_split /=.
      apply: eq_bigr=> i _; rewrite [g _]linearZ_LR hge !scalerA -scalerDl.
      by rewrite mulrDr [t * _]mulrC.
    rewrite hsh -(inner_coordinateE hB) linear_sum in h0.
    rewrite (eq_bigr (fun i => if i == j then B z (e j) * (inner_norm hB (f (e j)) + t) else 0)) in h0;
      last first.
      move=> i _; rewrite linearZ inner_coordinateE ho.
      case: (eqVneq i j)=> [->|hij]; first by change (B z (e j) * (inner_norm hB (f (e j)) + t) * 1 =
        B z (e j) * (inner_norm hB (f (e j)) + t)); rewrite mulr1.
      by change ((B z (e i) * (inner_norm hB (f (e i)) + t)) * 0 = 0); rewrite mulr0.
    rewrite -big_mkcond /= big_pred1_eq in h0.
    have hpos : inner_norm hB (f (e j)) + t != 0.
      by rewrite gt_eqF // ltr_wpDl ?inner_norm_nonnegative.
    by move: h0=> /eqP; rewrite mulf_eq0 (negbTE hpos) orbF=> /eqP.
  have hz0 : z = 0 by rewrite hexp; apply: big1=> i _; rewrite hc scale0r.
  by apply/eqP; rewrite -subr_eq0; apply/eqP.
- apply: le_lt_trans (_ : onorm _ <= t) _; last by rewrite /t ltr_pdivrMr ?ltr0n // ltr_pMr ?ltr1n.
  apply: operator_norm_least; first exact: ltW.
  move=> x; rewrite /= /linear_difference.
  have hval : linear_comp h (linear_shift_map g t) x = h (g x) + t *: h x.
    by rewrite /linear_comp /= /linear_shift linearD linearZ_LR.
  rewrite hval hhg addrC addKr.
  by rewrite inner_normZ (orthogonal_map_norm hB hB hh) gtr0_norm.
Qed.

End Estimates.
