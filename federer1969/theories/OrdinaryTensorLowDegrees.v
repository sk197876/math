(** Supporting connections for Federer 1.4.5, p. 20, the exceptional
    dimensions of the ordinary tensor product. Reuse the grading laws of
    1.2.1 and the exterior dimension theorem of 1.3.2. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlternatingCoordinates GradedSums
  FiniteExteriorPowers FiniteBasisCriterion ExteriorAnticommutativity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [graded_at_most_one_commutative]: supporting connection
    for Federer 1.4.5, p. 20. An anticommutative graded algebra concentrated
    in degrees zero and one is ordinarily commutative: products of two
    degree-one elements vanish in degree two. Use 1.2.1, p. 11. *)
Lemma graded_at_most_one_commutative (K : fieldType) (V : lmodType K)
    (G : grading V) (mu : V -> V -> V) :
    bilinear mu -> graded_product G mu -> graded_anticommutative G mu ->
    (forall p x, (1<p)%N -> homogeneous G p x -> x=0) ->
    commutative mu.
Proof.
move=> hm hg ha hz.
apply: (graded_induction (G:=G)) => [y|x x' hx hx' y|p x hx].
- by rewrite (bil0l hm) (bil0r hm).
- by rewrite (bilDl hm) (bilDr hm) hx hx'.
apply: (graded_induction (G:=G)) => [|y y' hy hy'|q y hy].
- by rewrite (bil0l hm) (bil0r hm).
- by rewrite (bilDl hm) (bilDr hm) hy hy'.
case: p hx => [|[|p]] hx.
- have h := ha 0 q x y hx hy.
  by rewrite mul0n expr0 scale1r in h.
- case: q hy => [|[|q]] hy.
  + have h := ha 1 0 x y hx hy.
    by rewrite muln0 expr0 scale1r in h.
  + have hxy := hz 2 (mu x y) (ltnSn 1) (hg 1 1 x y hx hy).
    have hyx := hz 2 (mu y x) (ltnSn 1) (hg 1 1 y x hy hx).
    by rewrite hxy hyx.
  + have hq : (1<q.+2)%N by [].
    have hy0 := hz q.+2 y hq hy.
    by rewrite hy0 (bil0l hm) (bil0r hm).
- have hp : (1<p.+2)%N by [].
  have hx0 := hz p.+2 x hp hx.
  by rewrite hx0 (bil0l hm) (bil0r hm).
Qed.

(** Source for [finite_exterior_homogeneous_above_dimension]: supporting
    connection for Federer 1.4.5, p. 20, using the zero-above-dimension
    assertion of 1.3.2, p. 15. Transfer the existing component theorem to
    an actual homogeneous vector in the whole exterior algebra. *)
Lemma finite_exterior_homogeneous_above_dimension (K : fieldType)
    (h2 : (1+1 : K) != 0) (V : lmodType K) n
    (e : 'I_n -> V) (he : is_basis e) p (x : exterior_space V) :
    (n<p)%N -> homogeneous (exterior_grading V) p x -> x=0.
Proof.
move=> hp hx.
have hz := @exterior_power_above_dimension K n V e he h2 p hp
  (component (exterior_grading V) p x).
have h := congr1 (@component_val K (exterior_space V)
  (exterior_grading V) p) hz.
by rewrite componentE hx linear0 in h.
Qed.

(** Source for [finite_covector_homogeneous_above_dimension]: supporting
    connection for Federer 1.4.5, p. 20. A form of degree above the source
    dimension vanishes on every exterior word, by 1.3.2 and the extension
    identification of 1.4.1, p. 17. No dual basis is reconstructed. *)
Lemma finite_covector_homogeneous_above_dimension (K : fieldType)
    (h2 : (1+1 : K) != 0) (V : lmodType K) n
    (e : 'I_n -> V) (he : is_basis e) p (f : A_star V K^o) :
    (n<p)%N -> homogeneous (A_star_grading V K^o) p f -> f=0.
Proof.
move=> hp hf.
have hz : form_component p f = 0.
  apply: form_ext => t; rewrite form_componentE form_zeroE.
  have hw := @exterior_word_homogeneous K V t.
  rewrite size_tuple in hw.
  have ht := finite_exterior_homogeneous_above_dimension h2 he hp hw.
  by rewrite ht linear0.
have h := form_componentK p f.
by rewrite hf hz linear0 in h; symmetry.
Qed.

(** Source for [zero_space_empty_basis]: supporting boundary connection
    for Federer 1.4.5, p. 20. A zero source has the empty basis; this
    supplies n=0 to the existing exterior dimension theorem. *)
Lemma zero_space_empty_basis (K : fieldType) (V : lmodType K) :
    (forall x : V, x=0) -> is_basis (fun _ : 'I_0 => (0 : V)).
Proof.
move=> hz; apply: finite_basis_criterion.
- move=> c hc i; by have := ltn_ord i; rewrite ltn0.
- move=> x; exists (fun _ => (0 : K)); rewrite big_ord0; exact: hz.
Qed.

(** Source for [small_exterior_algebra_commutative]: supporting
    exceptional case of Federer 1.4.5, p. 20. The exterior algebra of a
    space of dimension at most one is commutative, by 1.3.2 and the
    original anticommutative grading. Zero spaces are included. *)
Lemma small_exterior_algebra_commutative (K : fieldType)
    (h2 : (1+1 : K) != 0) (V : lmodType K) n
    (e : 'I_n -> V) (he : is_basis e) :
    (n<=1)%N ->
    commutative (@wedge K V).
Proof.
move=> hn.
have hz p (x : exterior_space V) : (1<p)%N ->
    homogeneous (exterior_grading V) p x -> x=0.
  move=> hp hx.
  exact: (@finite_exterior_homogeneous_above_dimension K h2 V n e he
    p x (leq_ltn_trans hn hp) hx).
exact (@graded_at_most_one_commutative K (exterior_space V)
  (exterior_grading V) (@wedge K V) (wedge_bilinear V)
  (@wedge_graded K V) (@exterior_anticommutative K V) hz).
Qed.

(** Source for [small_covector_algebra_commutative]: supporting exceptional
    case of Federer 1.4.5, p. 20. The alternating algebra on a space of
    dimension at most one has only degrees zero and one, so its ordinary
    product is commutative. *)
Lemma small_covector_algebra_commutative (K : fieldType)
    (h2 : (1+1 : K) != 0) (V : lmodType K) n
    (e : 'I_n -> V) (he : is_basis e) :
    (n<=1)%N ->
    commutative (@alternating_wedge K h2 V K^o
      (fun x y : K^o => x*y) (scalar_bilinear K)).
Proof.
move=> hn.
have hz p (x : A_star V K^o) : (1<p)%N ->
    homogeneous (A_star_grading V K^o) p x -> x=0.
  move=> hp hx.
  exact: (@finite_covector_homogeneous_above_dimension K h2 V n e he
    p x (leq_ltn_trans hn hp) hx).
exact (@graded_at_most_one_commutative K (A_star V K^o)
  (A_star_grading V K^o) (alternating_wedge h2 (scalar_bilinear K))
  (@alternating_wedge_bilinear K h2 V K^o
    (fun x y : K^o => x*y) (scalar_bilinear K))
  (@alternating_wedge_graded K h2 V K^o
    (fun x y : K^o => x*y) (scalar_bilinear K))
  (@alternating_wedge_anticommutative K h2 V K^o
    (fun x y : K^o => x*y) (scalar_bilinear K) (@mulrC K)) hz).
Qed.
