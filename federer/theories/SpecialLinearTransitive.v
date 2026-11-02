(** Federer (1969), 2.7.16, p. 135: "In case n >= 2 the special linear group
    SL(n, R) = GL(n, R) cap {f : det(f) = 1} acts transitively on R^n ~
    {0}". Federer gives no proof. The proof here is elementary linear
    algebra. The map replacing the k-th vector of the standard base by u has
    determinant u_k, by the permutation formula of 1.3.4, p. 16. If x_1 <>
    0, the map e_1 |-> x composed with the diagonal map multiplying the
    second coordinate by x_1^{-1} lies in SL(n, R) and sends e_1 to x; here
    n >= 2 is used. If x_1 = 0 and x_k <> 0, the shear z |-> z + (z_k / x_k)
    e_1, which lies in SL(n, R), first moves x to a vector with first
    coordinate 1. Indices start at 0, so Federer's e_1 is the basis vector
    of index 0. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From mathcomp Require Import fingroup perm.
From Federer Require Import FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct
  EuclideanCoordinateTopology LinearBasis TensorUP ExteriorDeterminant ExteriorLeibniz
  PermutationDeterminant EuclideanLinearMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Transitive.
Variable R : realType.
Variable n : nat.
Local Notation V := (R_n R n).
Local Notation eps := (@coordinate_basis R n).

(** Source for [column_replacement]: the base e_1, ..., e_n of R^n with
    the k-th vector replaced by u, supporting Federer 2.7.16, p. 135.
    Definition. *)
Definition column_replacement (k : 'I_n) (u : V) (i : 'I_n) : V := if i == k then u else eps i.

(** Source for [column_replacement_det]: the linear map sending e_k to u
    and e_i to e_i for i <> k has determinant u_k, by the permutation
    formula of Federer 1.3.4, p. 16; supporting 2.7.16, p. 135. *)
Lemma column_replacement_det (k : 'I_n) (u : V) :
  euclidean_det (euclidean_frame_map (column_replacement k u)) = u k.
Proof.
rewrite /euclidean_det (det_formula (euclidean_two_nonzero R) (@coordinate_basisP R n)
  (f := euclidean_frame_map (column_replacement k u)) (b := fun i j => column_replacement k u i j)); last first.
  move=> i; rewrite /= euclidean_frame_basis.
  exact: esym (euclidean_coordinate_expansion (column_replacement k u i)).
rewrite (bigD1 (1%g : 'S_n)) //= index_one ?euclidean_two_nonzero // mul1r.
rewrite [X in _ + X]big1 ?addr0.
  rewrite (bigD1 k) //= perm1 /column_replacement eqxx big1 ?mulr1 // => i hi.
  by rewrite perm1 (negbTE hi) /coordinate_basis ffunE eqxx.
move=> s hs.
have [j [hj hjk]] : exists j, s j != j /\ j != k.
  case: (pselect (exists i, s i != i))=> [[i hi]|hne].
  - case: (eqVneq i k)=> [hik|hik]; last by exists i.
    exists (s i); split; last by rewrite -hik; exact: hi.
    by apply/negP=> /eqP h; rewrite (perm_inj h) eqxx in hi.
  - exfalso; move: hs=> /eqP; apply.
    have hp : s =1 (1%g : 'S_n).
      move=> i; rewrite perm1; apply/eqP; apply: contrapT=> h; apply: hne; exists i; exact/negP.
    exact: (iffLR (permP s (1%g : 'S_n)) hp).
rewrite (bigD1 j) //= /column_replacement (negbTE hjk) /coordinate_basis ffunE.
by rewrite (negbTE hj) mul0r mulr0.
Qed.

End Transitive.

Section SpecialTransitive.
Variable R : realType.
Variable k : nat.
Local Notation n := k.+2.
Local Notation V := (R_n R n).
Local Notation eps := (@coordinate_basis R n).

(** Source for [second_index]: the index of the second coordinate of
    R^n, n >= 2, supporting Federer 2.7.16, p. 135. Definition. *)
Definition second_index : 'I_n := lift ord0 ord0.

(** Source for [second_scaling]: the diagonal map multiplying the second
    coordinate by c, supporting Federer 2.7.16, p. 135. Definition. *)
Definition second_scaling (c : R) : 'I_n -> R := fun i => if i == second_index then c else 1.

(** Source for [second_scaling_det]: the map multiplying the second
    coordinate by c has determinant c, Federer 1.3.4, p. 16. Supporting
    lemma. *)
Lemma second_scaling_det (c : R) : euclidean_det (euclidean_diagonal_map (second_scaling c)) = c.
Proof.
rewrite euclidean_diagonal_det (bigD1 second_index) //= /second_scaling eqxx big1 ?mulr1 //.
by move=> i hi; rewrite (negbTE hi).
Qed.

(** Source for [second_scaling_first]: the map multiplying the second
    coordinate fixes e_1, supporting Federer 2.7.16, p. 135. *)
Lemma second_scaling_first (c : R) : euclidean_diagonal_map (second_scaling c) (eps ord0) = eps ord0.
Proof.
apply/ffunP=> i; rewrite /= /euclidean_diagonal !ffunE /second_scaling.
case: (eqVneq i ord0)=> [->|hi]; first by rewrite /second_index /= mul1r.
by rewrite mulr0.
Qed.

(** Source for [special_linear_first_coordinate]: if x_1 <> 0 there is
    g in SL(n, R) with g(e_1) = x, supporting Federer 2.7.16, p. 135. *)
Lemma special_linear_first_coordinate (x : V) : x ord0 != 0 ->
  exists g : {linear V -> V}, euclidean_det g = 1 /\ g (eps ord0) = x.
Proof.
move=> hx.
pose C := euclidean_frame_map (column_replacement ord0 x).
pose D := euclidean_diagonal_map (second_scaling (x ord0)^-1).
exists (linear_comp C D); split.
- by rewrite euclidean_det_comp column_replacement_det second_scaling_det mulfV.
- rewrite /linear_comp /= second_scaling_first /C /= euclidean_frame_basis.
  by rewrite /column_replacement eqxx.
Qed.

(** Source for [shear_value]: the shear z |-> z + (z_j t) e_1 sends x to
    x + (x_j t) e_1, supporting Federer 2.7.16, p. 135. *)
Lemma shear_value (j : 'I_n) (t : R) (x : V) :
  euclidean_frame_map (column_replacement j (eps j + t *: eps ord0)) x = x + (x j * t) *: eps ord0.
Proof.
rewrite /= /euclidean_frame.
rewrite (eq_bigr (fun i => x i *: eps i + (if i == j then x i * t else 0) *: eps ord0)); last first.
  move=> i _; rewrite /column_replacement; case: (eqVneq i j)=> [->|hij].
  - by rewrite scalerDr scalerA.
  - by rewrite scale0r addr0.
rewrite big_split /= euclidean_coordinate_expansion -scaler_suml.
by rewrite -big_mkcond /= big_pred1_eq.
Qed.

(** Source for [special_linear_basis_image]: for every x <> 0 in R^n,
    n >= 2, there is g in SL(n, R) with g(e_1) = x, supporting Federer
    2.7.16, p. 135. *)
Lemma special_linear_basis_image (x : V) : x != 0 ->
  exists g : {linear V -> V}, euclidean_det g = 1 /\ g (eps ord0) = x.
Proof.
move=> hx; case: (eqVneq (x ord0) 0)=> [h0|h0]; last exact: special_linear_first_coordinate.
have [j hj] : exists j, x j != 0.
  apply: contrapT=> hne; apply: (negP hx); apply/eqP/ffunP=> i; rewrite ffunE.
  by apply: contrapT=> hi; apply: hne; exists i; exact/eqP.
have hj0 : j != ord0 by apply/eqP=> hj0; move: hj; rewrite hj0 h0 eqxx.
pose S := euclidean_frame_map (column_replacement j (eps j + (x j)^-1 *: eps ord0)).
have hdS : euclidean_det S = 1.
  by rewrite column_replacement_det /coordinate_basis !ffunE eqxx (negbTE hj0) scaler0 addr0.
have hSx : S x = x + eps ord0 by rewrite shear_value mulfV ?scale1r.
have hSx0 : (S x) ord0 != 0.
  by rewrite hSx /coordinate_basis !ffunE h0 eqxx add0r oner_eq0.
have [g' [hg' hg'e]] := special_linear_first_coordinate hSx0.
have hSi : injective S by apply/(euclidean_det_injective S).1; rewrite hdS oner_eq0.
have [T [hST hTS]] := euclidean_linear_inverse hSi.
have hdT : euclidean_det T = 1.
  by have := euclidean_det_inverse hST; rewrite hdS mulr1.
exists (linear_comp T g'); split.
- by rewrite euclidean_det_comp hdT hg' mulr1.
- by rewrite /linear_comp /= hg'e hST.
Qed.

(** Source for [special_linear_transitive]: Federer 2.7.16, p. 135, "In
    case n >= 2 the special linear group SL(n, R) acts transitively on
    R^n ~ {0}": for x, y in R^n ~ {0} there is f with det f = 1 and
    f(x) = y. Direct formalisation. *)
Theorem special_linear_transitive (x y : V) : x != 0 -> y != 0 ->
  exists f : {linear V -> V}, euclidean_det f = 1 /\ f x = y.
Proof.
move=> hx hy.
have [gx [hgx hgxe]] := special_linear_basis_image hx.
have [gy [hgy hgye]] := special_linear_basis_image hy.
have hi : injective gx by apply/(euclidean_det_injective gx).1; rewrite hgx oner_eq0.
have [hx' [h1 h2]] := euclidean_linear_inverse hi.
have hdx : euclidean_det hx' = 1 by have := euclidean_det_inverse h1; rewrite hgx mulr1.
exists (linear_comp gy hx'); split.
- by rewrite euclidean_det_comp hgy hdx mulr1.
- by rewrite /linear_comp /= -hgxe h1 hgye.
Qed.

End SpecialTransitive.

(** Source for [general_linear_transitive_punctured]: Federer 2.7.16,
    p. 135, "a transitive action results through replacement of R^n by
    R^n ~ {0}": for every n and x, y in R^n ~ {0} there is f with
    det f <> 0 and f(x) = y. For n = 1 a diagonal map suffices, and for
    n >= 2 [special_linear_transitive] applies. Direct formalisation. *)
Theorem general_linear_transitive_punctured (R : realType) n (x y : R_n R n) :
  x != 0 -> y != 0 -> exists f : {linear R_n R n -> R_n R n}, euclidean_det f != 0 /\ f x = y.
Proof.
case: n x y=> [|[|k]] x y hx hy.
- by move: hx; rewrite (coordinate_zero x) eqxx.
- have h0 (z : R_n R 1) : z != 0 -> z ord0 != 0.
    move=> hz; apply/negP=> /eqP h; apply: (negP hz); apply/eqP/ffunP=> i.
    by rewrite (ord1 i) h ffunE.
  have hx0 := h0 x hx; have hy0 := h0 y hy.
  exists (euclidean_diagonal_map (fun _ : 'I_1 => y ord0 / x ord0)); split.
  + by rewrite euclidean_diagonal_det big_ord1 mulf_neq0 ?invr_eq0.
  + apply/ffunP=> i; rewrite /= /euclidean_diagonal ffunE (ord1 i).
    by rewrite divfK.
- have [f [hf hfx]] := special_linear_transitive hx hy.
  by exists f; split=> //; rewrite hf oner_eq0.
Qed.
