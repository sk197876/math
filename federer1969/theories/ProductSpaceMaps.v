(** Federer (1969), 1.6.5, pp. 25-26: the four displayed maps, their
    relations, and the auxiliary vectors used in the proof. The maps are
    defined on the actual product vector space. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SimpleVectors InteriorNaturality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Module FedererProduct.
Section Maps.
Variable K : fieldType.
Variable V : lmodType K.
Local Notation W := (GRing.Lmodule.clone K (V * V)%type _).

(** Source for [P]: Federer 1.6.5, p. 25, displayed maps.
    Definition of the first inclusion x maps to (x,0). *)
Definition P (x : V) : W := (x,0).

(** Source for [P_linear]: Federer 1.6.5, p. 25, displayed linear maps.
    Supporting verification of linearity. *)
Lemma P_linear : linear P.
Proof. by move=> c x y; congr (_, _); rewrite linearZ /= scaler0 addr0. Qed.
HB.instance Definition _ := GRing.isLinear.Build K V W *:%R P P_linear.

(** Source for [P_map]: Federer 1.6.5, p. 25, displayed linear maps.
    The map packaged with its proved linearity. *)
Definition P_map : {linear V -> W} :=
  GRing.Linear.clone _ _ _ _ P _.

(** Source for [Q]: Federer 1.6.5, p. 25, displayed maps.
    Definition of the second inclusion x maps to (0,x). *)
Definition Q (x : V) : W := (0,x).

(** Source for [Q_linear]: Federer 1.6.5, p. 25, displayed linear maps.
    Supporting verification of linearity. *)
Lemma Q_linear : linear Q.
Proof. by move=> c x y; congr (_, _); rewrite linearZ /= scaler0 addr0. Qed.
HB.instance Definition _ := GRing.isLinear.Build K V W *:%R Q Q_linear.

(** Source for [Q_map]: Federer 1.6.5, p. 25, displayed linear maps.
    The map packaged with its proved linearity. *)
Definition Q_map : {linear V -> W} :=
  GRing.Linear.clone _ _ _ _ Q _.

(** Source for [g]: Federer 1.6.5, p. 25, displayed maps.
    Definition of the diagonal x maps to (x,x). *)
Definition g (x : V) : W := (x,x).

(** Source for [g_linear]: Federer 1.6.5, p. 25, displayed linear maps.
    Supporting verification of linearity. *)
Lemma g_linear : linear g.
Proof. by move=> c x y; congr (_, _). Qed.
HB.instance Definition _ := GRing.isLinear.Build K V W *:%R g g_linear.

(** Source for [g_map]: Federer 1.6.5, p. 25, displayed linear maps.
    The map packaged with its proved linearity. *)
Definition g_map : {linear V -> W} :=
  GRing.Linear.clone _ _ _ _ g _.

(** Source for [f]: Federer 1.6.5, p. 25, displayed maps.
    Definition of the difference (x,y) maps to x-y. *)
Definition f (x : W) : V := x.1-x.2.

(** Source for [f_linear]: Federer 1.6.5, p. 25, displayed linear maps.
    Supporting verification of linearity. *)
Lemma f_linear : linear f.
Proof. by move=> c x y; rewrite /f !linearP scalerBr addrACA /= scalerN. Qed.
HB.instance Definition _ := GRing.isLinear.Build K W V *:%R f f_linear.

(** Source for [f_map]: Federer 1.6.5, p. 25, displayed linear maps.
    The map packaged with its proved linearity. *)
Definition f_map : {linear W -> V} :=
  GRing.Linear.clone _ _ _ _ f _.

(** Source for [first]: Federer 1.6.5, p. 25, displayed maps.
    Definition of the first coordinate projection. *)
Definition first (x : W) : V := x.1.

(** Source for [first_linear]: Federer 1.6.5, p. 25, displayed linear maps.
    Supporting verification of linearity. *)
Lemma first_linear : linear first.
Proof. by move=> c x y; rewrite /first /=. Qed.
HB.instance Definition _ := GRing.isLinear.Build K W V *:%R first first_linear.

(** Source for [first_map]: Federer 1.6.5, p. 25, displayed linear maps.
    The map packaged with its proved linearity. *)
Definition first_map : {linear W -> V} :=
  GRing.Linear.clone _ _ _ _ first _.

(** Source for [second]: Federer 1.6.5, p. 25, displayed maps.
    Definition of the second coordinate projection. *)
Definition second (x : W) : V := x.2.

(** Source for [second_linear]: Federer 1.6.5, p. 25, displayed linear maps.
    Supporting verification of linearity. *)
Lemma second_linear : linear second.
Proof. by move=> c x y; rewrite /second /=. Qed.
HB.instance Definition _ := GRing.isLinear.Build K W V *:%R second second_linear.

(** Source for [second_map]: Federer 1.6.5, p. 25, displayed linear maps.
    The map packaged with its proved linearity. *)
Definition second_map : {linear W -> V} :=
  GRing.Linear.clone _ _ _ _ second _.

(** Source for [first_P]: Federer 1.6.5, p. 25, displayed maps.
    Supporting relation: the first projection is a left inverse of P. *)
Lemma first_P : cancel P first.
Proof. by []. Qed.

(** Source for [second_Q]: Federer 1.6.5, p. 25, displayed maps.
    Supporting relation: the second projection is a left inverse of Q. *)
Lemma second_Q : cancel Q second.
Proof. by []. Qed.

(** Source for [product_decomposition]: Federer 1.6.5, p. 25, displayed maps.
    Supporting relation: the product splits as the sum of its two coordinate subspaces. *)
Lemma product_decomposition : forall x : W, P (first x) + Q (second x) = x.
Proof. by case=> x y; congr (_, _); rewrite /P /Q /first /second /= ?addr0 ?add0r. Qed.

(** Source for [f_P]: Federer 1.6.5, p. 25, displayed maps.
    Supporting relation: f composed with P is the identity. *)
Lemma f_P : cancel P f.
Proof. by move=> x; rewrite /f /P /= subr0. Qed.

(** Source for [f_Q]: Federer 1.6.5, p. 25, displayed maps.
    Supporting relation: f composed with Q is negation. *)
Lemma f_Q : forall x, f (Q x) = -x.
Proof. by move=> x; rewrite /f /Q /= sub0r. Qed.

(** Source for [f_g]: Federer 1.6.5, p. 25, displayed maps.
    Supporting relation: the diagonal lies in the kernel of f. *)
Lemma f_g : forall x, f (g x) = 0.
Proof. by move=> x; rewrite /f /g /= subrr. Qed.

(** Source for [first_g]: Federer 1.6.5, p. 25, displayed maps.
    Supporting relation: the first projection is a left inverse of g. *)
Lemma first_g : cancel g first.
Proof. by []. Qed.

(** Source for [diagonal_kernel]: Federer 1.6.5, p. 25, displayed maps.
    Supporting relation: the kernel of the difference map is exactly the diagonal. *)
Lemma diagonal_kernel : forall x : W, f x = 0 <-> exists v, x = g v.
Proof. move=> [x y]; rewrite /f /g /=; split.
- move/subr0_eq=> ->; by exists y.
- by move=> [v [-> ->]]; rewrite subrr. Qed.

(** Source for [a]: Federer 1.6.5, p. 26, auxiliary vectors in the proof.
    Definition: a(v) is one half of (v,-v). *)
Definition a (x : V) : W := ((1+1 : K)^-1 *: x, - ((1+1 : K)^-1 *: x)).

(** Source for [a_linear]: Federer 1.6.5, p. 26, auxiliary vectors in the proof.
    Supporting verification that a is linear. *)
Lemma a_linear : linear a.
Proof.
move=> c x y; rewrite /a; congr (_, _); rewrite linearZ /=.
- by rewrite scalerDr !scalerA mulrC.
- by rewrite !scalerN scalerDr opprD !scalerA mulrC.
Qed.
HB.instance Definition _ := GRing.isLinear.Build K V W *:%R a a_linear.

(** Source for [a_map]: Federer 1.6.5, p. 26, auxiliary vectors in the proof.
    The auxiliary linear map packaged with its proved linearity. *)
Definition a_map : {linear V -> W} := GRing.Linear.clone _ _ _ _ a _.

(** Source for [f_a]: Federer 1.6.5, p. 26, auxiliary vectors in the proof.
    Supporting relation: applying f to a(v) gives v. *)
Lemma f_a (h2 : (1+1 : K) != 0) : cancel a f.
Proof.
move=> x; rewrite /f /a /= opprK -scalerDl -mulr2n -mulr_natl.
change (((1+1)*(1+1)^-1 : K) *: x = x).
by rewrite mulfV // scale1r.
Qed.

(** Source for [product_pair_wedge]: Federer 1.6.5, p. 26, identity P(e_j) wedge Q(e_j)=a_j wedge b_j.
    Direct identity for every vector, with b(v)=g(v). *)
Theorem product_pair_wedge (h2 : (1+1 : K) != 0) v :
  wedge (exterior_generator (P v)) (exterior_generator (Q v)) =
    wedge (exterior_generator (a v)) (exterior_generator (g v)).
Proof.
have ha : a v = (1+1 : K)^-1 *: (P v - Q v).
  by congr (_, _); rewrite !linearB /P /Q /= ?scaler0 ?subr0 ?sub0r ?scalerN.
have hg : g v = P v + Q v by congr (_, _); rewrite /P /Q /= ?addr0 ?add0r.
rewrite ha hg linearZ linearB linearD
  (bilZl (wedge_bilinear W)) (bilBl (wedge_bilinear W))
  !(bilDr (wedge_bilinear W)) !exterior_generator_square !add0r !addr0.
rewrite (exterior_generator_skew (Q v) (P v)) opprK.
have hh (z : exterior_space W) : z+z = (1+1 : K) *: z.
  by rewrite scalerDl scale1r.
rewrite hh.
by rewrite scalerA mulVf // scale1r.
Qed.

End Maps.
End FedererProduct.
