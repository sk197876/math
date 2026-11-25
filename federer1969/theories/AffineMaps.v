(** Federer (1969), 2.7.16, pp. 133–134, the elementary geometric concepts
    recalled before the examples: "A subset S of a vectorspace V is an
    affine subspace if and only if alpha v + beta w in S whenever v in S, w
    in S, alpha in R, beta in R and alpha + beta = 1; in case 0 in S, this
    means that S is a linear subspace of V. A function f on a vectorspace V
    into a vectorspace V' is an affine map if and only if f(alpha v + beta
    w) = alpha f(v) + beta f(w) whenever ..; this is equivalent to the
    condition that f is an affine subspace of V x V'; in case f(0) = 0 it
    means that f is linear. The class A(V, V') of all affine maps of V into
    V' is a vectorspace. Using the linear epimorphism L: A(V, V') -> Hom(V,
    V'), L(f)(v) = f(v) - f(0), we construct the linear isomorphism M: A(V,
    V') = Hom(V, V') (+) V', M(f) = (L(f), f(0)). In case V = V', L
    preserves functional composition, and the univalent map tau: V -> A(V,
    V), tau_z(v) = z + v for z, v in V, transforms vector addition into
    composition of maps. We observe that, whenever g in Hom(V, V) and z in
    V, M^{-1}(g, z) = tau_z o g, g o tau_z = tau_{g(z)} o g. Furthermore im
    tau = {f : L(f) = 1_V}." The scalars form a real field; the maps f are
    identified with their graphs {(v, f(v))}, and the vector space A(V, V')
    is the set of affine maps with the pointwise operations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Affine.
Variable R : numFieldType.
Variables V W : lmodType R.

(** Source for [is_affine_subspace]: "A subset S of a vectorspace V is
    an affine subspace if and only if alpha v + beta w in S whenever
    v in S, w in S, alpha in R, beta in R and alpha + beta = 1", Federer
    2.7.16, p. 133. Direct definition. *)
Definition is_affine_subspace (U : lmodType R) (S : set U) : Prop :=
  forall v w (a b : R), S v -> S w -> a + b = 1 -> S (a *: v + b *: w).

(** Source for [is_linear_subspace]: a linear subspace of V, Federer
    2.7.16, p. 133: S contains 0 and is closed under addition and
    scalar multiplication. Definition. *)
Definition is_linear_subspace (U : lmodType R) (S : set U) : Prop :=
  [/\ S 0, forall v w, S v -> S w -> S (v + w) & forall (a : R) v, S v -> S (a *: v)].

(** Source for [affine_subspace_linear]: "in case 0 in S, this means
    that S is a linear subspace of V", Federer 2.7.16, p. 133. Direct
    formalisation. *)
Theorem affine_subspace_linear (S : set V) :
  S 0 -> (is_affine_subspace S <-> is_linear_subspace S).
Proof.
move=> h0; split.
- move=> hS.
  have hscale (a : R) v : S v -> S (a *: v).
    move=> hv; have h := hS v 0 a (1 - a) hv h0 (subrKC a 1).
    by rewrite scaler0 addr0 in h.
  split=> // v w hv hw.
  have h2 : (2 : R) != 0 by rewrite pnatr_eq0.
  have hh : (2 : R)^-1 + 2^-1 = 1 by rewrite [RHS]splitr mul1r.
  have h := hS v w 2^-1 2^-1 hv hw hh.
  have := hscale 2 _ h; rewrite scalerDr !scalerA mulfV // !scale1r; exact.
- move=> [_ hadd hscale] v w a b hv hw _; apply: hadd; exact: hscale.
Qed.

(** Source for [is_affine_map]: "A function f on a vectorspace V into a
    vectorspace V' is an affine map if and only if
    f(alpha v + beta w) = alpha f(v) + beta f(w) whenever v in V, w in V,
    alpha in R, beta in R and alpha + beta = 1", Federer 2.7.16, p. 133.
    Direct definition. *)
Definition is_affine_map (f : V -> W) : Prop :=
  forall v w (a b : R), a + b = 1 -> f (a *: v + b *: w) = a *: f v + b *: f w.

(** Source for [function_graph]: the function f as a subset
    {(v, f(v))} of V x V', as in Federer 2.7.16, p. 133, "the condition
    that f is an affine subspace of V x V'". Definition. *)
Definition function_graph (f : V -> W) : set (V * W)%type := [set p | p.2 = f p.1].

(** Source for [affine_map_graph]: "this is equivalent to the condition
    that f is an affine subspace of V x V'", Federer 2.7.16, p. 133.
    Direct formalisation. *)
Theorem affine_map_graph (f : V -> W) : is_affine_map f <-> is_affine_subspace (function_graph f).
Proof.
split.
- move=> hf [v x] [w y] a b; rewrite /function_graph /= => -> -> hab; by rewrite hf.
- move=> hG v w a b hab.
  have h := hG (v, f v) (w, f w) a b erefl erefl hab.
  by rewrite /function_graph /= in h; rewrite -h.
Qed.

(** Source for [affine_map_zero_linear]: "in case f(0) = 0 it means
    that f is linear", Federer 2.7.16, p. 133. Direct formalisation. *)
Theorem affine_map_zero_linear (f : V -> W) : is_affine_map f -> f 0 = 0 -> linear f.
Proof.
move=> hf h0.
have hscale (a : R) v : f (a *: v) = a *: f v.
  have h := hf v 0 a (1 - a) (subrKC a 1).
  by rewrite scaler0 addr0 h0 scaler0 addr0 in h.
have h2 : (2 : R) != 0 by rewrite pnatr_eq0.
have hh : (2 : R)^-1 + 2^-1 = 1 by rewrite [RHS]splitr mul1r.
have hadd v w : f (v + w) = f v + f w.
  have h := hf (2 *: v) (2 *: w) 2^-1 2^-1 hh.
  by rewrite !scalerA mulVf // !scale1r !hscale !scalerA mulVf // !scale1r in h.
by move=> a v w; rewrite hadd hscale.
Qed.

(** Source for [linear_affine_map]: every linear map is affine,
    supporting Federer 2.7.16, p. 133 ("L is an epimorphism"). *)
Lemma linear_affine_map (f : {linear V -> W}) : is_affine_map f.
Proof. by move=> v w a b _; rewrite linearD !linearZ. Qed.

(** Source for [affine_map_add]: A(V, V') is closed under addition,
    "The class A(V, V') of all affine maps of V into V' is a
    vectorspace", Federer 2.7.16, p. 133. Supporting lemma. *)
Lemma affine_map_add (f g : V -> W) : is_affine_map f -> is_affine_map g ->
  is_affine_map (fun v => f v + g v).
Proof.
move=> hf hg v w a b hab; rewrite hf // hg // !scalerDr.
by rewrite addrACA.
Qed.

(** Source for [affine_map_scale]: A(V, V') is closed under scalar
    multiplication, Federer 2.7.16, p. 133. Supporting lemma. *)
Lemma affine_map_scale (c : R) (f : V -> W) : is_affine_map f -> is_affine_map (fun v => c *: f v).
Proof. by move=> hf v w a b hab; rewrite hf // scalerDr !scalerA mulrC (mulrC c). Qed.

(** Source for [affine_map_zero]: the zero map is affine, Federer
    2.7.16, p. 133. Supporting lemma. *)
Lemma affine_map_zero : is_affine_map (fun _ : V => (0 : W)).
Proof. by move=> v w a b _; rewrite !scaler0 addr0. Qed.

(** Source for [affine_linear_part]: "L(f)(v) = f(v) - f(0)", Federer
    2.7.16, p. 133. Direct definition. *)
Definition affine_linear_part (f : V -> W) (v : V) : W := f v - f 0.

(** Source for [affine_linear_part_linear]: L(f) is linear for every
    affine map f, so that L maps A(V, V') into Hom(V, V'), Federer
    2.7.16, p. 133. Direct formalisation. *)
Theorem affine_linear_part_linear (f : V -> W) : is_affine_map f -> linear (affine_linear_part f).
Proof.
move=> hf; apply: affine_map_zero_linear; last by rewrite /affine_linear_part subrr.
by apply: affine_map_add=> //; move=> v w a b hab; rewrite -scalerDl hab scale1r.
Qed.

(** Source for [affine_linear_part_additive]: L is linear,
    L(c f + g) = c L(f) + L(g), Federer 2.7.16, p. 133, "the linear
    epimorphism L". Supporting lemma. *)
Lemma affine_linear_part_additive (c : R) (f g : V -> W) (v : V) :
  affine_linear_part (fun x => c *: f x + g x) v = c *: affine_linear_part f v + affine_linear_part g v.
Proof. by rewrite /affine_linear_part scalerBr opprD addrACA. Qed.

(** Source for [affine_linear_part_onto]: L is an epimorphism: L(g) = g
    for linear g, Federer 2.7.16, p. 133. Direct formalisation. *)
Theorem affine_linear_part_onto (g : {linear V -> W}) (v : V) : affine_linear_part g v = g v.
Proof. by rewrite /affine_linear_part linear0 subr0. Qed.

(** Source for [affine_decomposition]: f(v) = f(0) + L(f)(v), the
    inverse of M, M^{-1}(L(f), f(0)) = f, Federer 2.7.16, p. 133.
    Direct formalisation. *)
Theorem affine_decomposition (f : V -> W) (v : V) : f v = f 0 + affine_linear_part f v.
Proof. by rewrite /affine_linear_part addrC subrK. Qed.

(** Source for [affine_isomorphism]: the map M(f) = (L(f), f(0)) of
    Federer 2.7.16, p. 133, is a linear isomorphism of A(V, V') onto
    Hom(V, V') (+) V': for every linear g and z in V' there is exactly
    one affine f with L(f) = g and f(0) = z, namely v |-> z + g(v).
    Direct formalisation of bijectivity; linearity of M is
    [affine_linear_part_additive]. *)
Theorem affine_isomorphism (g : {linear V -> W}) (z : W) :
  [/\ is_affine_map (fun v => z + g v), affine_linear_part (fun v => z + g v) =1 g,
    (fun v => z + g v) 0 = z &
    forall f, is_affine_map f -> affine_linear_part f =1 g -> f 0 = z -> f =1 (fun v => z + g v)].
Proof.
split.
- move=> v w a b hab; rewrite linearD !linearZ !scalerDr addrACA -scalerDl hab scale1r.
  by [].
- by move=> v; rewrite /affine_linear_part linear0 addr0 addrC addKr.
- by rewrite linear0 addr0.
- by move=> f _ hL h0 v; rewrite affine_decomposition hL h0.
Qed.

End Affine.

Section Translations.
Variable R : numFieldType.
Variable V : lmodType R.

(** Source for [affine_translation]: "tau: V -> A(V, V), tau_z(v) =
    z + v for z, v in V", Federer 2.7.16, p. 133. Direct definition. *)
Definition affine_translation (z v : V) : V := z + v.

(** Source for [affine_translation_affine]: each tau_z is affine,
    Federer 2.7.16, p. 133. Supporting lemma. *)
Lemma affine_translation_affine (z : V) : is_affine_map (affine_translation z).
Proof.
move=> v w a b hab; rewrite /affine_translation !scalerDr addrACA -scalerDl hab scale1r.
by [].
Qed.

(** Source for [affine_translation_injective]: "the univalent map tau",
    Federer 2.7.16, p. 133: tau_z = tau_w implies z = w. Direct
    formalisation. *)
Theorem affine_translation_injective (z w : V) : affine_translation z =1 affine_translation w -> z = w.
Proof. by move=> h; have := h 0; rewrite /affine_translation !addr0. Qed.

(** Source for [affine_translation_add]: tau "transforms vector
    addition into composition of maps", tau_{z+w} = tau_z o tau_w,
    Federer 2.7.16, p. 134. Direct formalisation. *)
Theorem affine_translation_add (z w : V) :
  affine_translation (z + w) =1 affine_translation z \o affine_translation w.
Proof. by move=> v; rewrite /affine_translation /= addrA. Qed.

(** Source for [affine_linear_part_comp]: "In case V = V', L preserves
    functional composition", L(f o g) = L(f) o L(g) for affine f and g,
    Federer 2.7.16, p. 133. Direct formalisation. *)
Theorem affine_linear_part_comp (f g : V -> V) : is_affine_map f -> is_affine_map g ->
  affine_linear_part (f \o g) =1 affine_linear_part f \o affine_linear_part g.
Proof.
move=> hf hg v.
have hl := affine_linear_part_linear hf.
have hsub a b : affine_linear_part f (a - b) = affine_linear_part f a - affine_linear_part f b.
  by rewrite addrC -scaleN1r hl scaleN1r addrC.
rewrite /= [affine_linear_part g v]/affine_linear_part hsub /affine_linear_part.
by rewrite opprB addrA subrK.
Qed.

(** Source for [affine_translation_compose]: Federer 2.7.16, p. 134,
    "M^{-1}(g, z) = tau_z o g, g o tau_z = tau_{g(z)} o g" for g in
    Hom(V, V) and z in V. Direct formalisation of both displayed
    identities. *)
Theorem affine_translation_compose (g : {linear V -> V}) (z : V) :
  (forall v, (affine_translation z \o g) v = z + g v) /\
  g \o affine_translation z =1 affine_translation (g z) \o g.
Proof. by split=> // v; rewrite /= /affine_translation linearD. Qed.

(** Source for [affine_translation_image]: "Furthermore
    im tau = {f : L(f) = 1_V}", Federer 2.7.16, p. 134: an affine map f
    is a translation tau_z if and only if L(f) is the identity, and then
    z = f(0). Direct formalisation. *)
Theorem affine_translation_image (f : V -> V) : is_affine_map f ->
  ((exists z, f =1 affine_translation z) <-> affine_linear_part f =1 id).
Proof.
move=> hf; split.
- move=> [z hz] v; by rewrite /affine_linear_part !hz /affine_translation addr0 addrC addKr.
- move=> hL; exists (f 0)=> v; by rewrite affine_decomposition hL.
Qed.

(** Source for [affine_univalent_iff]: the affine group of V, "the
    ... subset of univalent maps in A(V, V), which equals
    L^{-1}(linear group of V)", Federer 2.7.16, p. 134: an affine map is
    univalent if and only if its linear part is univalent. Direct
    formalisation of the equality of the two sets. *)
Theorem affine_univalent_iff (f : V -> V) : injective f <-> injective (affine_linear_part f).
Proof.
split=> hf v w h.
- by apply: hf; move: h; rewrite /affine_linear_part=> /addIr.
- apply: hf; rewrite /affine_linear_part h.
  by [].
Qed.

End Translations.
