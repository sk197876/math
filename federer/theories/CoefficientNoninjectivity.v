(** Federer 1.4.4, p. 20, coefficient-algebra parenthesis. The printed
    noninjectivity claim needs V nonzero and commutative coefficients.
    The missing general proof uses the one-form product of 1.4.2 and
    independence of exterior products from 1.3.2. The existing separation
    and independent-product lemmas supply these steps. No basis of the
    whole source or coefficient space is assumed. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From Federer Require Import AlternatingCoordinates CoefficientCoordinates
  HomTensor OneFormIdentification OneFormCommutator OmegaConstruction
  FiniteIndependence PairingSeparation IndependentProducts
  FiniteBasisCriterion InfiniteSequence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section RankOne.
Variable K : fieldType.
Variables V W : lmodType K.

(** Source for [coefficient_rank_one_injective]: supporting connection for
    Federer 1.4.4, p. 20. If ell(v)=1, evaluation at v recovers the
    coefficient of the one-form x |-> ell(x) w. This uses the canonical
    map of 1.1.4, p. 11, rather than constructing another Hom space. *)
Lemma coefficient_rank_one_injective (ell : Hom V K^o) v :
    ell v = 1 -> injective (hom_tensor_pair (W:=W) ell).
Proof.
move=> hv a b hab.
have h := congr1 (fun f : Hom V W => f v) hab.
by rewrite /hom_tensor_pair !hom_with_coefficientE hv !scale1r in h.
Qed.

(** The linear structure is the right-variable law already proved for
    the canonical dual-tensor pairing in Federer 1.1.4. *)
HB.instance Definition _ (ell : Hom V K^o) :=
  GRing.isLinear.Build K W (Hom V W) *:%R (hom_tensor_pair (W:=W) ell)
    ((@hom_tensor_bilinear K V W).2 ell).

(** Source for [coefficient_rank_one_independent]: supporting connection
    for Federer 1.4.4, p. 20. Independent coefficients give independent
    one-forms with a common normalized scalar factor. Apply the existing
    preservation of independence under an injective linear map. *)
Lemma coefficient_rank_one_independent (ell : Hom V K^o) v
    (I : finType) (e : I -> W) :
    ell v = 1 -> finite_independent e ->
    finite_independent (fun i => hom_tensor_pair ell (e i)).
Proof.
move=> hv he.
apply: (@finite_independent_map K I W (Hom V W)
  (GRing.Linear.clone _ _ _ _ (hom_tensor_pair ell) _) e) => //.
exact: coefficient_rank_one_injective hv.
Qed.
End RankOne.

Section Coefficients.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable W : algebra K.
Hypothesis hcomm : commutative (alg_mul W).

(** Source for [coefficient_one_form_product_two]: supporting connection
    for Federer 1.4.4, p. 20, using 1.4.2, pp. 18-19. The homogeneous
    product of two one-forms has value a(v)b(w)-a(w)b(v). This merely
    transfers the existing full alternating-algebra formula. *)
Lemma coefficient_one_form_product_two (a b : Hom V W) v w :
    form_wedge h2 (alg_bilinear W) (one_form a) (one_form b) [tuple v; w] =
    alg_mul W (a v) (b w) - alg_mul W (a w) (b v).
Proof.
have h : form_wedge h2 (alg_bilinear W) (one_form a) (one_form b)
    [tuple v; w] =
    alternating_wedge h2 (alg_bilinear W) (one_generator a)
      (one_generator b) (exterior_word [tuple v; w]).
  by rewrite /one_generator -form_wedge_include form_includeE
    form_extensionE form_wordsE.
by rewrite h one_forms_wedge_two.
Qed.

(** Source for [coefficient_rank_one_product_zero]: supporting connection
    for the corrected noninjectivity assertion in Federer 1.4.4, p. 20.
    One-forms x |-> ell(x)a and x |-> ell(x)b have zero alternating
    product, by the preceding two-one-form formula and bilinearity. *)
Lemma coefficient_rank_one_product_zero (ell : Hom V K^o) a b :
    alternating_wedge h2 (alg_bilinear W)
      (one_generator (hom_tensor_pair ell a))
      (one_generator (hom_tensor_pair ell b)) = 0.
Proof.
rewrite /one_generator -form_wedge_include.
have hz : form_wedge h2 (alg_bilinear W)
    (one_form (hom_tensor_pair ell a))
    (one_form (hom_tensor_pair ell b)) = 0.
  apply: form_ext => /tupleP [v /tupleP [w t]].
  rewrite (tuple0 t) form_zeroE coefficient_one_form_product_two.
  rewrite /hom_tensor_pair !hom_with_coefficientE.
  rewrite !(@bilZl K W W W (alg_mul W) (alg_bilinear W))
    !(@bilZr K W W W (alg_mul W) (alg_bilinear W)) !scalerA.
  by rewrite mulrC subrr.
by rewrite hz linear0.
Qed.

(** Source for [Omega_W_not_injective]: corrected assertion from Federer
    1.4.4, p. 20, coefficient-algebra parenthesis. For a nonzero source
    and two independent coefficient vectors, the scalar-based Omega has
    a nonzero kernel element. A normalized functional supplies the two
    independent one-forms; their exterior product is nonzero, while their
    alternating product vanishes. No finite-dimensional hypothesis is
    imposed. The excluded zero-source case has an existing counterexample. *)
Theorem Omega_W_not_injective (v : V) (e : 'I_2 -> W) :
    v != 0 -> finite_independent e ->
    ~ injective (Omega_W h2 V hcomm).
Proof.
move=> hv he hinj.
have [ell hell] := nonzero_functional hv.
have hi := coefficient_rank_one_independent hell he.
have hn := @independent_word_nonzero K h2 (Hom V W) 2
  (fun i => hom_tensor_pair ell (e i)) hi.
have hidx : lift ord0 (ord0 : 'I_1) = (ord_max : 'I_2).
  by apply: val_inj.
have hs : [seq hom_tensor_pair ell (e i) | i <- enum 'I_2] =
    [:: hom_tensor_pair ell (e ord0); hom_tensor_pair ell (e ord_max)].
  by rewrite !enum_ordSl enum_ord0 /= hidx.
rewrite hs in hn.
have hz : Omega_W h2 V hcomm
    (exterior_word [:: hom_tensor_pair ell (e ord0);
      hom_tensor_pair ell (e ord_max)]) = 0.
  rewrite !exterior_word_cons exterior_word_nil wedge_unitr
    Omega_W_wedge !Omega_W_generator.
  exact: coefficient_rank_one_product_zero.
have hzero : exterior_word [:: hom_tensor_pair ell (e ord0);
    hom_tensor_pair ell (e ord_max)] = 0.
  apply: hinj; by rewrite hz linear0.
by rewrite hzero eqxx in hn.
Qed.

(** Source for [Omega_W_injective_requires_coefficient_unit]: supporting
    boundary case for Federer 1.4.4, p. 20. Injectivity forces the
    coefficient unit to be nonzero, because Omega preserves units and the
    scalar exterior algebra always has a nonzero unit. This also covers
    the zero coefficient algebra, which has no independent pair. *)
Lemma Omega_W_injective_requires_coefficient_unit :
    injective (Omega_W h2 V hcomm) -> alg_one W != 0.
Proof.
move=> hinj; apply/eqP => hu.
have hz : exterior_unit (Hom V W) = 0.
  apply: hinj; by rewrite Omega_W_one hu !linear0.
by move: (exterior_unit_nonzero (Hom V W)); rewrite hz eqxx.
Qed.

(** Source for [Omega_W_injective_requires_coefficient_line]: corrected
    necessity assertion from Federer 1.4.4, p. 20. For V nonzero,
    injectivity implies that the coefficient unit is a one-element basis
    of W. Otherwise an additional coefficient extends the independent
    unit to a pair, contradicting the preceding kernel theorem. The
    existing independent-family extension and finite-basis criterion are
    reused. This states dimension one without assuming finite dimension. *)
Theorem Omega_W_injective_requires_coefficient_line (v : V) :
    v != 0 -> injective (Omega_W h2 V hcomm) ->
    is_basis (fun _ : 'I_1 => alg_one W).
Proof.
move=> hv hinj.
have hu := Omega_W_injective_requires_coefficient_unit hinj.
have hi : finite_independent (fun _ : 'I_1 => alg_one W).
  move=> c hc i; rewrite big_ord1 in hc.
  have hc0 : c ord0 = 0.
    move/eqP: hc; by rewrite scaler_eq0 (negbTE hu) orbF => /eqP.
  by rewrite (ord1 i).
have hspan (w : W) : exists c : K, w = c *: alg_one W.
  have [h|h] := pselect (exists c : K, w = c *: alg_one W).
    exact: h.
  have hout (c : 'I_1 -> K) : w != \sum_i c i *: alg_one W.
    apply/eqP => hc; apply: h; exists (c ord0).
    by rewrite big_ord1 in hc.
  have hpair := @finite_independent_snoc K W 1
    (fun _ : 'I_1 => alg_one W) w hi hout.
  exfalso; exact: (Omega_W_not_injective hv hpair hinj).
apply: finite_basis_criterion hi _ => w.
have [c hc] := hspan w; exists (fun _ => c).
by rewrite big_ord1.
Qed.

(** Source for [Omega_W_noninjective_unless_coefficient_line]: corrected
    general noninjectivity conclusion from Federer 1.4.4, p. 20. With
    V nonzero and W commutative, Omega is not injective unless dim W=1,
    expressed by the actual singleton unit basis. Zero and infinite
    coefficient dimensions are included. The zero-source exception and
    the failures of the other printed coefficient assertions remain. *)
Theorem Omega_W_noninjective_unless_coefficient_line (v : V) :
    v != 0 -> ~ is_basis (fun _ : 'I_1 => alg_one W) ->
    ~ injective (Omega_W h2 V hcomm).
Proof.
move=> hv hn hinj; apply: hn.
exact: Omega_W_injective_requires_coefficient_line hv hinj.
Qed.
End Coefficients.
