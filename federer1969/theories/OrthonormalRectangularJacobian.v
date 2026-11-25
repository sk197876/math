(** Federer (1969), 3.2.28(3), p. 266:
    the exterior norm of the displayed diagonal rectangular
    tangent map is the product of its nonzero singular
    coefficients. The adjoint reduces the norm to a
    top-degree product, using 1.7.5–1.7.6, pp. 32–34. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import TensorUP Hom Bilinear InnerProductUP InnerProductLaws InnerNorm InnerNormalization
  OrthonormalFamilies OrthonormalBilinearCoordinates LinearBasis FiniteOrdinalBasis
  AdjointUP Adjoint AdjointLaws ExteriorGrading ExteriorMaps FiniteExteriorPowers ExteriorNorm ExteriorOperatorNorm
  ExteriorOperatorEstimate TopExteriorNorm InnerExterior InnerExteriorPositivity ExteriorHadamardEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [orthonormal_rectangular_exterior_jacobian]:
    the calculation J S=2^((1-m)/2) in Federer
    3.2.28(3), p. 266, abstracted from its
    displayed orthonormal source/target bases. The actual
    coefficient pairings determine the linear map's
    q-th exterior operator norm; zero and empty
    coefficient families are included. *)
Theorem orthonormal_rectangular_exterior_jacobian (R:realType)
    (h2:(1+1:R)!=0) (V W:lmodType R) (B:V->V->R) (C:W->W->R)
    (hB:is_inner_product B) (hC:is_inner_product C) (I:finType)
    (e:I->V) (he:is_basis e) (hE:orthonormal_family B e)
    q (b:'I_q->W) (hb:is_basis b) (hO:orthonormal_family C b)
    (iota:'I_q->I) (lambda:'I_q->R) (f:{linear V->W}):
  injective iota ->(forall j,0<=lambda j) ->
  (forall i j,C (f (e i)) (b j)=if i==iota j then lambda j else 0) ->
  exterior_operator_norm h2 hB hC (finite_ordinal_basis he) f q=\prod_j lambda j.
Proof.
move=>hI hL hPair.
pose A:=@inner_adjoint R V W B C hB hC #|I|
  (fun i=>e (enum_val i)) (finite_ordinal_basis he) f.
have hAdj:is_adjoint B C f A:=inner_adjointP hB hC (finite_ordinal_basis he) f.
have hAll j:forall x,C (f x) (b j)=B x (lambda j*:e (iota j)).
  apply:(basis_induction he).
  - by rewrite linear0 !(bil0l (inner_bilinear hB)) !(bil0l (inner_bilinear hC)).
  - move=>x y hx hy; by rewrite linearD (bilDl (inner_bilinear hC))
      (bilDl (inner_bilinear hB)) hx hy.
  - move=>c x hx; by rewrite linearZ (bilZl (inner_bilinear hC))
      (bilZl (inner_bilinear hB)) hx.
  - move=>i; rewrite hPair (bilZr (inner_bilinear hB)) hE.
    change ((if i==iota j then lambda j else 0)=lambda j*(if i==iota j then 1 else 0)).
    by case:(i==iota j); rewrite ?mulr0 ?mulr1.
have hA j:A (b j)=lambda j*:e (iota j).
  apply:(inner_vectors_ext hB)=>x; rewrite hAdj; exact:hAll.
have hOrth i j:i!=j ->B (A (b i)) (A (b j))=0.
  move=>hij; rewrite !hA (bilZl (inner_bilinear hB)) (bilZr (inner_bilinear hB)) hE
    (inj_eq hI) (negbTE hij).
  change (lambda i*(lambda j*0)=0); by rewrite !mulr0.
have hNorm j:inner_norm hB (A (b j))=lambda j.
  by rewrite hA inner_normZ (ger0_norm (hL j)) (orthonormal_norm1 hB hE) mulr1.
pose z:=e_lambda b (ord_tuple q).
have hUnit:exterior_norm h2 hC z= 1:=orthonormal_product_unit_norm h2 hC hO.
rewrite (@exterior_operator_adjoint_norm_equal R h2 V W B C hB hC
  #|I| q (fun i=>e (enum_val i)) b (finite_ordinal_basis he) hb f A hAdj q).
rewrite (@top_exterior_operator_unit_value R h2 W V C B hC hB q b hb A z hUnit)
  /z exterior_map_indexed_product (orthogonal_product_norm h2 hB hOrth).
by apply:eq_bigr=>j _; exact:hNorm.
Qed.

(** Source for [orthonormal_rectangular_finite_exterior_jacobian]:
    the same rectangular diagonal calculation with the
    finite pair-indexed bases printed in Federer
    3.2.28(3), pp. 265–266. Ordinal enumeration
    changes neither the operator norm nor the product. *)
Theorem orthonormal_rectangular_finite_exterior_jacobian (R:realType)
    (h2:(1+1:R)!=0) (V W:lmodType R) (B:V->V->R) (C:W->W->R)
    (hB:is_inner_product B) (hC:is_inner_product C) (I J:finType)
    (e:I->V) (he:is_basis e) (hE:orthonormal_family B e)
    (b:J->W) (hb:is_basis b) (hO:orthonormal_family C b)
    (iota:J->I) (lambda:J->R) (f:{linear V->W}):
  injective iota ->(forall j,0<=lambda j) ->
  (forall i j,C (f (e i)) (b j)=if i==iota j then lambda j else 0) ->
  exterior_operator_norm h2 hB hC (finite_ordinal_basis he) f #|J|=\prod_j lambda j.
Proof.
move=>hI hL hPair.
have hOB:orthonormal_family C (fun j:'I_#|J|=>b (enum_val j)).
  by move=>i j; rewrite hO (inj_eq (@enum_val_inj J predT)).
have hInj:injective (fun j:'I_#|J|=>iota (enum_val j)).
  move=>i j h; exact:(@enum_val_inj J predT i j (hI _ _ h)).
have hResult:=@orthonormal_rectangular_exterior_jacobian R h2 V W B C hB hC I e he hE
  #|J| (fun j=>b (enum_val j)) (finite_ordinal_basis hb) hOB
  (fun j=>iota (enum_val j)) (fun j=>lambda (enum_val j)) f hInj
  (fun j=>hL (enum_val j)) (fun i j=>hPair i (enum_val j)).
by rewrite -(big_enum_val lambda) in hResult.
Qed.

(** Source for [orthonormal_surviving_direction_pairing]:
    the displayed three surviving directions and one
    zero case determine all matrix coefficients,
    Federer 3.2.28(3), p. 266. The kernel
    directions are disjoint from the matched directions. *)
Lemma orthonormal_surviving_direction_pairing (R:realType)
    (V W:lmodType R) (C:W->W->R) (hC:is_inner_product C) (I J:finType)
    (e:I->V) (b:J->W) (hO:orthonormal_family C b)
    (iota:J->I) (lambda:J->R) (f:{linear V->W}) (K:pred I):
  injective iota ->(forall j,~~K (iota j)) ->
  (forall i,(exists j,i=iota j) \/K i) ->
  (forall j,f (e (iota j))=lambda j*:b j) ->
  (forall i,K i ->f (e i)=0) ->
  forall i j,C (f (e i)) (b j)=if i==iota j then lambda j else 0.
Proof.
move=>hI hDisjoint hCover hImages hZero i j.
case:(hCover i)=>[[l ->]|hK].
- rewrite hImages (bilZl (inner_bilinear hC)) hO (inj_eq hI).
  change (lambda l*(if l==j then 1 else 0)=if l==j then lambda j else 0).
  case:(eqVneq l j)=>[->|hNe]; by rewrite ?eqxx ?(negbTE hNe) ?mulr0 ?mulr1.
- rewrite (hZero i hK) (bil0l (inner_bilinear hC)).
  have hNe:i!=iota j.
    apply/eqP=>he; move:hK; rewrite he; by move/negP:(hDisjoint j); apply.
  by rewrite (negbTE hNe).
Qed.
